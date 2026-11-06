import Calderon.FischerContraction
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def polynomialContraction (f : σ → ℝ) (q : σ → MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ := ∑ i : σ, C (f i) * q i

def directionalDerivative (f : σ → ℝ) (v : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ := polynomialContraction f (fun i => pderiv i v)

lemma fischerInner_polynomialContraction_left (f : σ → ℝ)
    (q : σ → MvPolynomial σ ℝ) (s : MvPolynomial σ ℝ) :
    fischerInner (polynomialContraction f q) s = ∑ i : σ, f i * fischerInner (q i) s := by
  simp [polynomialContraction, fischerInner_sum_left, fischerInner_C_mul_left]

lemma fischerInner_self_add_le (p q : MvPolynomial σ ℝ) :
    fischerInner (p + q) (p + q) ≤ 2 * fischerInner p p + 2 * fischerInner q q := by
  have h := two_mul_fischerInner_le p q
  simp only [fischerInner_add_left, fischerInner_add_right]
  rw [fischerInner_symm q p]
  linarith

lemma fischerInner_polynomialContraction_self_le_of_pos (f : σ → ℝ)
    (q : σ → MvPolynomial σ ℝ) (hB : 0 < ∑ i : σ, f i ^ 2) :
    fischerInner (polynomialContraction f q) (polynomialContraction f q) ≤
      (∑ i : σ, f i ^ 2) * ∑ i : σ, fischerInner (q i) (q i) := by
  classical
  let B := ∑ i : σ, f i ^ 2
  let s := polynomialContraction f q
  have hBn : B ≠ 0 := ne_of_gt hB
  have hc : (∑ i : σ, f i * fischerInner (q i) s) = fischerInner s s := by
    rw [← fischerInner_polynomialContraction_left]
  have hpos : 0 ≤ ∑ i : σ,
      fischerInner (q i - C (B⁻¹ * f i) * s) (q i - C (B⁻¹ * f i) * s) :=
    Finset.sum_nonneg fun i _ => fischerInner_self_nonneg _
  have hexp : (∑ i : σ,
      fischerInner (q i - C (B⁻¹ * f i) * s) (q i - C (B⁻¹ * f i) * s)) =
      (∑ i : σ, fischerInner (q i) (q i)) -
      2 * B⁻¹ * (∑ i : σ, f i * fischerInner (q i) s) +
      B⁻¹ ^ 2 * (∑ i : σ, f i ^ 2) * fischerInner s s := by
    calc
      _ = ∑ i : σ, (fischerInner (q i) (q i) -
          2 * B⁻¹ * (f i * fischerInner (q i) s) + B⁻¹ ^ 2 * f i ^ 2 * fischerInner s s) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [fischerInner_sub_left, fischerInner_sub_right,
          fischerInner_C_mul_left, fischerInner_C_mul_right]
        rw [fischerInner_symm s (q i)]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul]
  rw [hexp, hc] at hpos
  change 0 ≤ (∑ i : σ, fischerInner (q i) (q i)) -
    2 * B⁻¹ * fischerInner s s + B⁻¹ ^ 2 * B * fischerInner s s at hpos
  have hb := mul_nonneg (le_of_lt hB) hpos
  rw [mul_add, mul_sub] at hb
  have hcancel : B * (2 * B⁻¹ * fischerInner s s) -
      B * (B⁻¹ ^ 2 * B * fischerInner s s) = fischerInner s s := by
    field_simp [hBn]
    <;> ring
  change fischerInner s s ≤ B * ∑ i : σ, fischerInner (q i) (q i)
  linarith

lemma fischerInner_polynomialContraction_self_le (f : σ → ℝ)
    (q : σ → MvPolynomial σ ℝ) :
    fischerInner (polynomialContraction f q) (polynomialContraction f q) ≤
      (∑ i : σ, f i ^ 2) * ∑ i : σ, fischerInner (q i) (q i) := by
  classical
  have hB : 0 ≤ ∑ i : σ, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hB.eq_or_lt with hB | hB
  · have hf : ∀ i, f i = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))).mp hB.symm
      intro i
      have hi := hz i (Finset.mem_univ i)
      nlinarith [sq_nonneg (f i)]
    simp [polynomialContraction, hf, fischerInner_zero_left]
  · exact fischerInner_polynomialContraction_self_le_of_pos f q hB

lemma fischerInner_directionalDerivative_self_le {k : ℕ} (f : σ → ℝ)
    (v : MvPolynomial σ ℝ) (hv : v.IsHomogeneous k) :
    fischerInner (directionalDerivative f v) (directionalDerivative f v) ≤
      (∑ i : σ, f i ^ 2) * (k : ℝ) * fischerInner v v := by
  have h := fischerInner_polynomialContraction_self_le f (fun i => pderiv i v)
  rw [sum_fischerInner_pderiv_self hv] at h
  simpa only [directionalDerivative, mul_assoc] using h

/-- Actual degree-weighted polynomial derivative with prescribed base derivative value. -/
def weightedDerivativePlus (k : ℕ) (f : σ → ℝ) (v : MvPolynomial σ ℝ)
    (w : σ → MvPolynomial σ ℝ) (i : σ) : MvPolynomial σ ℝ :=
  w i + C (k : ℝ) * (C (f i) * v)

def weightedDerivativeMinus (k : ℕ) (f : σ → ℝ) (v : MvPolynomial σ ℝ)
    (w : σ → MvPolynomial σ ℝ) (i : σ) : MvPolynomial σ ℝ :=
  -w i + C (k : ℝ) * (C (f i) * v)

lemma polynomialDivergence_weightedDerivativePlus (k : ℕ) (f : σ → ℝ)
    (v : MvPolynomial σ ℝ) (w : σ → MvPolynomial σ ℝ) :
    polynomialDivergence (weightedDerivativePlus k f v w) = polynomialDivergence w +
      C (k : ℝ) * directionalDerivative f v := by
  simp [weightedDerivativePlus, polynomialDivergence, directionalDerivative,
    polynomialContraction, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma polynomialDivergence_weightedDerivativeMinus (k : ℕ) (f : σ → ℝ)
    (v : MvPolynomial σ ℝ) (w : σ → MvPolynomial σ ℝ) :
    polynomialDivergence (weightedDerivativeMinus k f v w) = -polynomialDivergence w +
      C (k : ℝ) * directionalDerivative f v := by
  simp [weightedDerivativeMinus, polynomialDivergence, directionalDerivative,
    polynomialContraction, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma polynomialDivergence_weightedDerivative_relation (k : ℕ) (f : σ → ℝ)
    (v : MvPolynomial σ ℝ) (w : σ → MvPolynomial σ ℝ) :
    polynomialDivergence (weightedDerivativePlus k f v w) =
      -polynomialDivergence (weightedDerivativeMinus k f v w) +
        C (2 * (k : ℝ)) * directionalDerivative f v := by
  rw [polynomialDivergence_weightedDerivativePlus, polynomialDivergence_weightedDerivativeMinus]
  simp only [map_mul, map_ofNat]
  ring

lemma fischerInner_neg_left (p q : MvPolynomial σ ℝ) :
    fischerInner (-p) q = -fischerInner p q := by
  rw [fischerInner_symm, fischerInner_neg_right, fischerInner_symm]

lemma fischerInner_weightedDerivative_divergence_bound {k : ℕ} (f : σ → ℝ)
    (v : MvPolynomial σ ℝ) (w : σ → MvPolynomial σ ℝ) (hv : v.IsHomogeneous k)
    (beta : ℝ) (hf : ∑ i : σ, f i ^ 2 ≤ beta ^ 2) :
    fischerInner (polynomialDivergence (weightedDerivativePlus k f v w))
      (polynomialDivergence (weightedDerivativePlus k f v w)) ≤
      2 * fischerInner (polynomialDivergence (weightedDerivativeMinus k f v w))
        (polynomialDivergence (weightedDerivativeMinus k f v w)) +
      8 * (k : ℝ) ^ 3 * beta ^ 2 * fischerInner v v := by
  have hd := fischerInner_directionalDerivative_self_le f v hv
  have hmul := mul_le_mul_of_nonneg_right hf
    (mul_nonneg (Nat.cast_nonneg k) (fischerInner_self_nonneg v))
  have hd' : fischerInner (directionalDerivative f v) (directionalDerivative f v) ≤
      (k : ℝ) * beta ^ 2 * fischerInner v v := by nlinarith
  have hs := fischerInner_self_add_le
    (-polynomialDivergence (weightedDerivativeMinus k f v w))
    (C (2 * (k : ℝ)) * directionalDerivative f v)
  rw [← polynomialDivergence_weightedDerivative_relation] at hs
  simp only [fischerInner_neg_left, fischerInner_neg_right, neg_neg,
    fischerInner_C_mul_left, fischerInner_C_mul_right] at hs
  have hm := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 8 * (k : ℝ) ^ 2 by positivity)
  nlinarith

lemma fischerInner_weightedDerivative_convex_bound {k : ℕ} (hk : 1 ≤ k)
    (f : σ → ℝ) (v : MvPolynomial σ ℝ) (w : σ → MvPolynomial σ ℝ)
    (hv : v.IsHomogeneous k) (hw : ∀ i, (w i).IsHomogeneous k)
    (beta zeta : ℝ) (hf : ∑ i : σ, f i ^ 2 ≤ beta ^ 2)
    (hz : 0 ≤ zeta) (hz' : zeta ≤ 1) :
    fischerInner (polynomialDivergence (weightedDerivativePlus k f v w))
      (polynomialDivergence (weightedDerivativePlus k f v w)) ≤
      (1 - zeta) * (((k : ℝ) + Fintype.card σ - 1) *
        ∑ i : σ, fischerInner (weightedDerivativePlus k f v w i)
          (weightedDerivativePlus k f v w i)) +
      zeta * (2 * fischerInner (polynomialDivergence (weightedDerivativeMinus k f v w))
        (polynomialDivergence (weightedDerivativeMinus k f v w)) +
        8 * (k : ℝ) ^ 3 * beta ^ 2 * fischerInner v v) := by
  have hp : ∀ i, (weightedDerivativePlus k f v w i).IsHomogeneous k := by
    intro i
    exact (hw i).add ((hv.C_mul (f i)).C_mul (k : ℝ))
  have h1 := fischerInner_divergence_self_le hk (weightedDerivativePlus k f v w) hp
  have h2 := fischerInner_weightedDerivative_divergence_bound f v w hv beta hf
  have h1' := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hz')
  have h2' := mul_le_mul_of_nonneg_left h2 hz
  nlinarith

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_directionalDerivative_self_le

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_weightedDerivative_convex_bound
