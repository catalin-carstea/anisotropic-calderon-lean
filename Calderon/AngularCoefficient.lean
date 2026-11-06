import Calderon.AngularFunctional

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

/-- The exact probability-sphere normalization from the source; sphere realization is separate. -/
def sphereNormalization (n k : ℕ) : ℝ := ∏ j ∈ Finset.range k, ((n : ℝ) + 2 * (j : ℝ))

@[simp] lemma sphereNormalization_zero (n : ℕ) : sphereNormalization n 0 = 1 := by
  simp [sphereNormalization]

lemma sphereNormalization_succ (n k : ℕ) :
    sphereNormalization n (k + 1) = ((n : ℝ) + 2 * (k : ℝ)) * sphereNormalization n k := by
  simp [sphereNormalization, Finset.prod_range_succ, mul_comm]

lemma sphereNormalization_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < sphereNormalization n k := by
  apply Finset.prod_pos
  intro j hj
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  positivity

lemma sphereNormalization_ratio {n : ℕ} (hn : 0 < n) (k : ℕ) :
    sphereNormalization n (k + 1) / sphereNormalization n k = (n : ℝ) + 2 * (k : ℝ) := by
  rw [sphereNormalization_succ]
  exact mul_div_cancel_right₀ _ (ne_of_gt (sphereNormalization_pos hn k))

def normalizedFischerInner (k : ℕ) (p q : MvPolynomial σ ℝ) : ℝ :=
  fischerInner p q / sphereNormalization (Fintype.card σ) k

def normalizedFischerSquare (k : ℕ) (p : MvPolynomial σ ℝ) : ℝ :=
  normalizedFischerInner k p p

lemma normalizedFischerSquare_nonneg (k : ℕ) (p : MvPolynomial σ ℝ) :
    0 ≤ normalizedFischerSquare k p := by
  exact div_nonneg (fischerInner_self_nonneg _) (Finset.prod_nonneg fun j _ => by positivity)

lemma normalizedFischerSquare_eq_zero_iff [Nonempty σ] (k : ℕ) (p : MvPolynomial σ ℝ) :
    normalizedFischerSquare k p = 0 ↔ p = 0 := by
  rw [normalizedFischerSquare, normalizedFischerInner, div_eq_zero_iff]
  simp [ne_of_gt (sphereNormalization_pos Fintype.card_pos k), fischerInner_self_eq_zero_iff]

lemma normalizedFischer_divergence_bound [Nonempty σ] (k : ℕ)
    (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).IsHomogeneous (k + 1)) :
    normalizedFischerSquare k (polynomialDivergence q) ≤
      (((k : ℝ) + Fintype.card σ) * ((Fintype.card σ : ℝ) + 2 * k)) *
        ∑ i : σ, normalizedFischerSquare (k + 1) (q i) := by
  have h := fischerInner_divergence_self_le (k := k + 1) (by omega) q hq
  have hN := sphereNormalization_pos (n := Fintype.card σ) Fintype.card_pos k
  have hNs := sphereNormalization_pos (n := Fintype.card σ) Fintype.card_pos (k + 1)
  have hc : 0 < (Fintype.card σ : ℝ) + 2 * k := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hd := div_le_div_of_nonneg_right h (le_of_lt hN)
  change fischerInner (polynomialDivergence q) (polynomialDivergence q) /
    sphereNormalization (Fintype.card σ) k ≤ _
  convert hd using 1
  simp only [normalizedFischerSquare, normalizedFischerInner, ← Finset.sum_div,
    sphereNormalization_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

def coefficientLowering (q : ℕ → σ → MvPolynomial σ ℝ) (k : ℕ) : MvPolynomial σ ℝ :=
  polynomialDivergence (q k)

def coefficientRaising (q : ℕ → σ → MvPolynomial σ ℝ) (k : ℕ) : MvPolynomial σ ℝ :=
  C ((Fintype.card σ : ℝ) + 2 * (k + 1)) * harmonicRaising k (q k)

lemma fischerInner_harmonicRaising_le [Nonempty σ] (k : ℕ)
    (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).IsHomogeneous (k + 1))
    (hΔ : ∀ i, laplacian (q i) = 0) :
    fischerInner (harmonicRaising k q) (harmonicRaising k q) ≤
      ((k : ℝ) + 2) * ∑ i : σ, fischerInner (q i) (q i) := by
  have hc := radiusSq_laplacian_coefficient_pos (σ := σ) k
  have hn := fischerInner_harmonicRaising_self (k := k + 1) q hq hΔ
    (by simpa using ne_of_gt hc)
  have hx := sum_fischerInner_pderiv_cross_le q hq
  have hs := fischerInner_self_nonneg (polynomialDivergence q)
  have hcorr : 0 ≤ 4 / (4 * (k : ℝ) + 2 * (Fintype.card σ : ℝ)) *
      fischerInner (polynomialDivergence q) (polynomialDivergence q) :=
    mul_nonneg (div_nonneg (by norm_num) (le_of_lt hc)) hs
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hn hx
  rw [hn]
  nlinarith

lemma normalizedFischer_harmonicRaising_bound [Nonempty σ] (k : ℕ)
    (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).IsHomogeneous (k + 1))
    (hΔ : ∀ i, laplacian (q i) = 0) :
    normalizedFischerSquare (k + 2)
      (C ((Fintype.card σ : ℝ) + 2 * (k + 1)) * harmonicRaising k q) ≤
      (((Fintype.card σ : ℝ) + 2 * (k + 1)) * ((k : ℝ) + 2)) *
        ∑ i : σ, normalizedFischerSquare (k + 1) (q i) := by
  have hn := fischerInner_harmonicRaising_le k q hq hΔ
  have hN := sphereNormalization_pos (n := Fintype.card σ) Fintype.card_pos (k + 1)
  have hc : 0 < (Fintype.card σ : ℝ) + 2 * (k + 1) := by
    have hcard : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hmul := mul_le_mul_of_nonneg_left hn (le_of_lt hc)
  have hd := div_le_div_of_nonneg_right hmul (le_of_lt hN)
  unfold normalizedFischerSquare normalizedFischerInner
  simp only [fischerInner_C_mul_left, fischerInner_C_mul_right]
  convert hd using 1
  · rw [show k + 2 = (k + 1) + 1 by omega, sphereNormalization_succ]
    push_cast
    field_simp
  · rw [← Finset.sum_div]
    ring

lemma coefficientLowering_homogeneous (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1)) (k : ℕ) :
    (coefficientLowering q k).IsHomogeneous k := by
  simpa [coefficientLowering] using polynomialDivergence_isHomogeneous (q k) (hq k)

lemma coefficientRaising_homogeneous (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1)) (k : ℕ) :
    (coefficientRaising q k).IsHomogeneous (k + 2) := by
  have h := harmonicRaising_isHomogeneous (k := k + 1) (by omega) (q k) (hq k)
  simpa [coefficientRaising, Nat.add_assoc] using h.C_mul ((Fintype.card σ : ℝ) + 2 * (k + 1))

lemma fischerInner_harmonicRaising_adjoint (k : ℕ) (q : σ → MvPolynomial σ ℝ)
    (h : MvPolynomial σ ℝ) (hΔ : laplacian h = 0) :
    fischerInner (harmonicRaising k q) h = ∑ i : σ, fischerInner (q i) (pderiv i h) := by
  rw [harmonicRaising, mul_assoc, fischerInner_sub_left, fischerInner_C_mul_left,
    fischerInner_radiusSq_mul_left, hΔ, fischerInner_zero_right, mul_zero, sub_zero]
  simp [polynomialRaising, fischerInner_sum_left, fischerInner_X_mul_left]

lemma normalizedFischer_raising_adjoint [Nonempty σ] (k : ℕ)
    (q : σ → MvPolynomial σ ℝ) (h : MvPolynomial σ ℝ) (hΔ : laplacian h = 0) :
    normalizedFischerInner (k + 2)
      (C ((Fintype.card σ : ℝ) + 2 * (k + 1)) * harmonicRaising k q) h =
      ∑ i : σ, normalizedFischerInner (k + 1) (q i) (pderiv i h) := by
  unfold normalizedFischerInner
  rw [fischerInner_C_mul_left, fischerInner_harmonicRaising_adjoint k q h hΔ,
    ← Finset.sum_div, show k + 2 = (k + 1) + 1 by omega, sphereNormalization_succ]
  have hc : (Fintype.card σ : ℝ) + 2 * (k + 1) ≠ 0 := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  push_cast
  field_simp

def loweringEnergyBudget (weight : ℕ → ℝ) (q : ℕ → σ → MvPolynomial σ ℝ) (k : ℕ) : ℝ :=
  weight k * ((((k : ℝ) + Fintype.card σ) * ((Fintype.card σ : ℝ) + 2 * k)) *
    ∑ i : σ, normalizedFischerSquare (k + 1) (q k i))

def raisingEnergyBudget (weight : ℕ → ℝ) (q : ℕ → σ → MvPolynomial σ ℝ) (k : ℕ) : ℝ :=
  weight k * ((((Fintype.card σ : ℝ) + 2 * (k + 1)) * ((k : ℝ) + 2)) *
    ∑ i : σ, normalizedFischerSquare (k + 1) (q k i))

lemma coefficientLowering_summable [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1))
    (hb : Summable (loweringEnergyBudget weight q)) :
    Summable (fun k => weight k * normalizedFischerSquare k (coefficientLowering q k)) := by
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hw k) (normalizedFischerSquare_nonneg k _))
    (fun k => mul_le_mul_of_nonneg_left (normalizedFischer_divergence_bound k (q k) (hq k)) (hw k)) hb

theorem coefficientLowering_tsum_bound [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1))
    (hb : Summable (loweringEnergyBudget weight q)) :
    (∑' k, weight k * normalizedFischerSquare k (coefficientLowering q k)) ≤
      ∑' k, loweringEnergyBudget weight q k := by
  exact (coefficientLowering_summable weight hw q hq hb).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (normalizedFischer_divergence_bound k (q k) (hq k)) (hw k)) hb

lemma coefficientRaising_summable [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1)) (hΔ : ∀ k i, laplacian (q k i) = 0)
    (hb : Summable (raisingEnergyBudget weight q)) :
    Summable (fun k => weight k * normalizedFischerSquare (k + 2) (coefficientRaising q k)) := by
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hw k) (normalizedFischerSquare_nonneg (k + 2) _))
    (fun k => mul_le_mul_of_nonneg_left
      (normalizedFischer_harmonicRaising_bound k (q k) (hq k) (hΔ k)) (hw k)) hb

theorem coefficientRaising_tsum_bound [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (hq : ∀ k i, (q k i).IsHomogeneous (k + 1)) (hΔ : ∀ k i, laplacian (q k i) = 0)
    (hb : Summable (raisingEnergyBudget weight q)) :
    (∑' k, weight k * normalizedFischerSquare (k + 2) (coefficientRaising q k)) ≤
      ∑' k, raisingEnergyBudget weight q k := by
  exact (coefficientRaising_summable weight hw q hq hΔ hb).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left
      (normalizedFischer_harmonicRaising_bound k (q k) (hq k) (hΔ k)) (hw k)) hb

/-- Exact series identity; interpretation as a Hilbert adjoint requires realization and domains. -/
theorem coefficientRaising_tsum_adjoint [Nonempty σ] (weight : ℕ → ℝ)
    (q : ℕ → σ → MvPolynomial σ ℝ) (h : ℕ → MvPolynomial σ ℝ)
    (hΔ : ∀ k, laplacian (h k) = 0) :
    (∑' k, weight k * normalizedFischerInner (k + 2) (coefficientRaising q k) (h k)) =
      ∑' k, weight k * ∑ i : σ, normalizedFischerInner (k + 1) (q k i) (pderiv i (h k)) := by
  apply tsum_congr
  intro k
  rw [coefficientRaising, normalizedFischer_raising_adjoint k (q k) (h k) (hΔ k)]

lemma normalizedFischer_lowering_eq [Nonempty σ] (k : ℕ) (q : σ → MvPolynomial σ ℝ) :
    normalizedFischerSquare k (polynomialDivergence q) =
      ((Fintype.card σ : ℝ) + 2 * k) *
        fischerInner (polynomialDivergence q) (polynomialDivergence q) /
          sphereNormalization (Fintype.card σ) (k + 1) := by
  unfold normalizedFischerSquare normalizedFischerInner
  rw [sphereNormalization_succ]
  have hc : (Fintype.card σ : ℝ) + 2 * k ≠ 0 := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  field_simp

lemma normalizedFischer_raising_eq [Nonempty σ] (k : ℕ) (q : σ → MvPolynomial σ ℝ) :
    normalizedFischerSquare (k + 2)
      (C ((Fintype.card σ : ℝ) + 2 * (k + 1)) * harmonicRaising k q) =
      ((Fintype.card σ : ℝ) + 2 * (k + 1)) *
        fischerInner (harmonicRaising k q) (harmonicRaising k q) /
          sphereNormalization (Fintype.card σ) (k + 1) := by
  unfold normalizedFischerSquare normalizedFischerInner
  rw [fischerInner_C_mul_left, fischerInner_C_mul_right,
    show k + 2 = (k + 1) + 1 by omega, sphereNormalization_succ]
  have hc : (Fintype.card σ : ℝ) + 2 * (k + 1) ≠ 0 := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  push_cast
  field_simp

theorem normalizedFischer_fock_difference [Nonempty σ] (k : ℕ)
    (qp qm : σ → MvPolynomial σ ℝ) (hqp : ∀ i, (qp i).IsHomogeneous (k + 1))
    (hΔ : ∀ i, laplacian (qp i) = 0) :
    normalizedFischerSquare (k + 2)
      (C ((Fintype.card σ : ℝ) + 2 * (k + 1)) * harmonicRaising k qp) -
      normalizedFischerSquare k (polynomialDivergence qm) =
      (((Fintype.card σ : ℝ) + 2 * (k + 1)) *
        ((∑ i : σ, fischerInner (qp i) (qp i)) +
          (∑ i : σ, ∑ j : σ, fischerInner (pderiv j (qp i)) (pderiv i (qp j))) -
          (4 / (4 * (k : ℝ) + 2 * (Fintype.card σ : ℝ))) *
            fischerInner (polynomialDivergence qp) (polynomialDivergence qp)) -
        ((Fintype.card σ : ℝ) + 2 * k) *
          fischerInner (polynomialDivergence qm) (polynomialDivergence qm)) /
        sphereNormalization (Fintype.card σ) (k + 1) := by
  rw [normalizedFischer_raising_eq, normalizedFischer_lowering_eq, ← sub_div]
  have hc := radiusSq_laplacian_coefficient_pos (σ := σ) k
  have hh := fischerInner_harmonicRaising_self (k := k + 1) qp hqp hΔ
    (by simpa using ne_of_gt hc)
  simpa using congrArg (fun x : ℝ =>
    (((Fintype.card σ : ℝ) + 2 * (k + 1)) * x -
      ((Fintype.card σ : ℝ) + 2 * k) *
        fischerInner (polynomialDivergence qm) (polynomialDivergence qm)) /
      sphereNormalization (Fintype.card σ) (k + 1)) hh

lemma sphereNormalization_three_initial :
    sphereNormalization 3 0 = 1 ∧ sphereNormalization 3 1 = 3 ∧
    sphereNormalization 3 2 = 15 ∧ sphereNormalization 3 3 = 105 := by
  norm_num [sphereNormalization, Finset.prod_range_succ]

lemma sphereNormalization_three_ratio (k : ℕ) :
    sphereNormalization 3 (k + 1) / sphereNormalization 3 k = 2 * (k : ℝ) + 3 := by
  rw [sphereNormalization_ratio (by omega)]
  norm_num
  ring

lemma abs_fischerInner_le (p q : MvPolynomial σ ℝ) :
    |fischerInner p q| ≤ (fischerInner p p + fischerInner q q) / 2 := by
  have h1 := two_mul_fischerInner_le p q
  have h2 := two_mul_fischerInner_le p (-q)
  simp only [fischerInner_neg_left, fischerInner_neg_right, neg_neg] at h2
  apply abs_le.mpr
  constructor <;> linarith

lemma abs_normalizedFischerInner_le [Nonempty σ] (k : ℕ) (p q : MvPolynomial σ ℝ) :
    |normalizedFischerInner k p q| ≤
      (normalizedFischerSquare k p + normalizedFischerSquare k q) / 2 := by
  have hN := sphereNormalization_pos (n := Fintype.card σ) Fintype.card_pos k
  have h := div_le_div_of_nonneg_right (abs_fischerInner_le p q) (le_of_lt hN)
  simp only [normalizedFischerSquare, normalizedFischerInner]
  rw [abs_div, abs_of_pos hN]
  convert h using 1 <;> ring

lemma abs_normalizedFischer_vectorPairing_le [Nonempty σ] (k : ℕ)
    (q r : σ → MvPolynomial σ ℝ) :
    |∑ i : σ, normalizedFischerInner k (q i) (r i)| ≤
      ((∑ i : σ, normalizedFischerSquare k (q i)) +
        (∑ i : σ, normalizedFischerSquare k (r i))) / 2 := by
  calc
    _ ≤ ∑ i : σ, |normalizedFischerInner k (q i) (r i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : σ, (normalizedFischerSquare k (q i) + normalizedFischerSquare k (r i)) / 2 :=
      Finset.sum_le_sum fun i _ => abs_normalizedFischerInner_le k (q i) (r i)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

def coefficientGradient (h : ℕ → MvPolynomial σ ℝ) (k : ℕ) (i : σ) : MvPolynomial σ ℝ :=
  pderiv i (h k)

lemma normalizedFischer_gradient_square_eq [Nonempty σ] (k : ℕ) (h : MvPolynomial σ ℝ)
    (hh : h.IsHomogeneous (k + 2)) :
    (∑ i : σ, normalizedFischerSquare (k + 1) (pderiv i h)) =
      (((k : ℝ) + 2) * ((Fintype.card σ : ℝ) + 2 * (k + 1))) *
        normalizedFischerSquare (k + 2) h := by
  unfold normalizedFischerSquare normalizedFischerInner
  rw [← Finset.sum_div, sum_fischerInner_pderiv_self hh,
    show k + 2 = (k + 1) + 1 by omega, sphereNormalization_succ (Fintype.card σ) (k + 1)]
  have hc : (Fintype.card σ : ℝ) + 2 * (k + 1) ≠ 0 := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  push_cast
  field_simp
  <;> ring

theorem coefficientGradient_tsum_square_eq [Nonempty σ] (weight : ℕ → ℝ)
    (h : ℕ → MvPolynomial σ ℝ) (hh : ∀ k, (h k).IsHomogeneous (k + 2)) :
    (∑' k, weight k * ∑ i : σ, normalizedFischerSquare (k + 1) (coefficientGradient h k i)) =
      ∑' k, weight k * ((((k : ℝ) + 2) * ((Fintype.card σ : ℝ) + 2 * (k + 1))) *
        normalizedFischerSquare (k + 2) (h k)) := by
  apply tsum_congr
  intro k
  simp only [coefficientGradient]
  rw [normalizedFischer_gradient_square_eq k (h k) (hh k)]

lemma coefficientAdjoint_pairing_abs_summable [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (h : ℕ → MvPolynomial σ ℝ)
    (hq : Summable (fun k => weight k * ∑ i : σ, normalizedFischerSquare (k + 1) (q k i)))
    (hh : Summable (fun k => weight k * ∑ i : σ, normalizedFischerSquare (k + 1) (coefficientGradient h k i))) :
    Summable (fun k => |weight k * ∑ i : σ,
      normalizedFischerInner (k + 1) (q k i) (coefficientGradient h k i)|) := by
  have hb := (hq.add hh).div_const 2
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ hb
  intro k
  rw [abs_mul, abs_of_nonneg (hw k)]
  have hp := mul_le_mul_of_nonneg_left
    (abs_normalizedFischer_vectorPairing_le (k + 1) (q k) (coefficientGradient h k)) (hw k)
  convert hp using 1 <;> ring

lemma coefficientRaising_pairing_abs_summable [Nonempty σ] (weight : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ weight k) (q : ℕ → σ → MvPolynomial σ ℝ)
    (h : ℕ → MvPolynomial σ ℝ) (hΔ : ∀ k, laplacian (h k) = 0)
    (hq : Summable (fun k => weight k * ∑ i : σ, normalizedFischerSquare (k + 1) (q k i)))
    (hh : Summable (fun k => weight k * ∑ i : σ, normalizedFischerSquare (k + 1) (coefficientGradient h k i))) :
    Summable (fun k => |weight k * normalizedFischerInner (k + 2) (coefficientRaising q k) (h k)|) := by
  have hpair := coefficientAdjoint_pairing_abs_summable weight hw q h hq hh
  convert hpair using 1
  funext k
  rw [coefficientRaising, normalizedFischer_raising_adjoint k (q k) (h k) (hΔ k)]
  rfl

/-- Concrete first drift correction in the normalized radial trace; PDE realization is separate. -/
def firstTraceCorrection (m : ℕ) (b : σ → ℝ) (v : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  if m = 0 then 0 else
    C (-(2 * (m : ℝ) + (Fintype.card σ : ℝ) - 2)⁻¹) * directionalDerivative b v

@[simp] lemma firstTraceCorrection_zero (b : σ → ℝ) (v : MvPolynomial σ ℝ) :
    firstTraceCorrection 0 b v = 0 := by simp [firstTraceCorrection]

lemma firstTraceCorrection_succ (k : ℕ) (b : σ → ℝ) (v : MvPolynomial σ ℝ) :
    firstTraceCorrection (k + 1) b v =
      C (-((Fintype.card σ : ℝ) + 2 * k)⁻¹) * directionalDerivative b v := by
  simp only [firstTraceCorrection, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

lemma normalizedFischer_firstTraceCorrection_eq [Nonempty σ] (k : ℕ)
    (b : σ → ℝ) (v : MvPolynomial σ ℝ) :
    normalizedFischerSquare k (firstTraceCorrection (k + 1) b v) =
      fischerInner (directionalDerivative b v) (directionalDerivative b v) /
        (((Fintype.card σ : ℝ) + 2 * k) * sphereNormalization (Fintype.card σ) (k + 1)) := by
  rw [firstTraceCorrection_succ]
  simp only [normalizedFischerSquare, normalizedFischerInner,
    fischerInner_C_mul_left, fischerInner_C_mul_right, sphereNormalization_succ]
  have hc : (Fintype.card σ : ℝ) + 2 * k ≠ 0 := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  field_simp
  <;> ring

theorem normalizedFischer_firstTraceCorrection_bound [Nonempty σ] (k : ℕ)
    (b : σ → ℝ) (v : MvPolynomial σ ℝ) (hv : v.IsHomogeneous (k + 1)) :
    normalizedFischerSquare k (firstTraceCorrection (k + 1) b v) ≤
      (((k : ℝ) + 1) / ((Fintype.card σ : ℝ) + 2 * k)) *
        (∑ i : σ, b i ^ 2) * normalizedFischerSquare (k + 1) v := by
  have hc : 0 < (Fintype.card σ : ℝ) + 2 * k := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hN := sphereNormalization_pos (n := Fintype.card σ) Fintype.card_pos (k + 1)
  have h := div_le_div_of_nonneg_right (fischerInner_directionalDerivative_self_le b v hv)
    (le_of_lt (mul_pos hc hN))
  rw [normalizedFischer_firstTraceCorrection_eq]
  convert h using 1
  simp only [normalizedFischerSquare, normalizedFischerInner, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

theorem normalizedFischer_firstTraceCorrection_uniform [Nonempty σ]
    (hn : 2 ≤ Fintype.card σ) (k : ℕ) (b : σ → ℝ)
    (v : MvPolynomial σ ℝ) (hv : v.IsHomogeneous (k + 1)) :
    normalizedFischerSquare k (firstTraceCorrection (k + 1) b v) ≤
      (1 / 2 : ℝ) * (∑ i : σ, b i ^ 2) * normalizedFischerSquare (k + 1) v := by
  have hc : 0 < (Fintype.card σ : ℝ) + 2 * k := by
    have hcard : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    positivity
  have hn' : 2 ≤ (Fintype.card σ : ℝ) := by exact_mod_cast hn
  have hratio : ((k : ℝ) + 1) / ((Fintype.card σ : ℝ) + 2 * k) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hc).mpr
    linarith
  have hB : 0 ≤ ∑ i : σ, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  have hmul := mul_le_mul_of_nonneg_right hratio
    (mul_nonneg hB (normalizedFischerSquare_nonneg (k + 1) v))
  have h := normalizedFischer_firstTraceCorrection_bound k b v hv
  nlinarith

lemma directionalDerivative_degree_zero (b : σ → ℝ) (v : MvPolynomial σ ℝ)
    (hv : v.IsHomogeneous 0) : directionalDerivative b v = 0 := by
  have h := fischerInner_directionalDerivative_self_le b v hv
  simp only [Nat.cast_zero, mul_zero, zero_mul] at h
  apply (fischerInner_self_eq_zero_iff _).mp
  exact le_antisymm h (fischerInner_self_nonneg _)

theorem firstTraceCorrection_abs_summable [Nonempty σ] (hn : 2 ≤ Fintype.card σ)
    (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k) (b : σ → ℝ)
    (v : ℕ → MvPolynomial σ ℝ) (hv : ∀ k, (v k).IsHomogeneous (k + 1))
    (hs : Summable (fun k => weight k * normalizedFischerSquare (k + 1) (v k))) :
    Summable (fun k => weight k * normalizedFischerSquare k (firstTraceCorrection (k + 1) b (v k))) := by
  have hb := hs.mul_left ((1 / 2 : ℝ) * ∑ i : σ, b i ^ 2)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hw k) (normalizedFischerSquare_nonneg k _)) _ hb
  intro k
  have h := mul_le_mul_of_nonneg_left
    (normalizedFischer_firstTraceCorrection_uniform hn k b (v k) (hv k)) (hw k)
  convert h using 1 <;> ring

theorem firstTraceCorrection_tsum_bound [Nonempty σ] (hn : 2 ≤ Fintype.card σ)
    (weight : ℕ → ℝ) (hw : ∀ k, 0 ≤ weight k) (b : σ → ℝ)
    (v : ℕ → MvPolynomial σ ℝ) (hv : ∀ k, (v k).IsHomogeneous (k + 1))
    (hs : Summable (fun k => weight k * normalizedFischerSquare (k + 1) (v k))) :
    (∑' k, weight k * normalizedFischerSquare k (firstTraceCorrection (k + 1) b (v k))) ≤
      ((1 / 2 : ℝ) * ∑ i : σ, b i ^ 2) *
        ∑' k, weight k * normalizedFischerSquare (k + 1) (v k) := by
  have hb := hs.mul_left ((1 / 2 : ℝ) * ∑ i : σ, b i ^ 2)
  rw [← tsum_mul_left]
  apply (firstTraceCorrection_abs_summable hn weight hw b v hv hs).tsum_le_tsum _ hb
  intro k
  have h := mul_le_mul_of_nonneg_left
    (normalizedFischer_firstTraceCorrection_uniform hn k b (v k) (hv k)) (hw k)
  convert h using 1 <;> ring

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.normalizedFischer_divergence_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.normalizedFischer_harmonicRaising_bound

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.sphereNormalization_ratio
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.coefficientLowering_tsum_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.coefficientRaising_tsum_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.coefficientRaising_tsum_adjoint

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.normalizedFischer_fock_difference

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.coefficientGradient_tsum_square_eq
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.coefficientRaising_pairing_abs_summable

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.normalizedFischer_firstTraceCorrection_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.firstTraceCorrection_tsum_bound
