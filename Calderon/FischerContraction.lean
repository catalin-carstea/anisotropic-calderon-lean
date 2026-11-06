import Calderon.FischerEstimates

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

lemma sum_fischerInner_X_mul_self {m : ℕ} {s : MvPolynomial σ ℝ}
    (hs : s.IsHomogeneous m) :
    (∑ i : σ, fischerInner (X i * s) (X i * s)) =
      ((m : ℝ) + (Fintype.card σ : ℝ)) * fischerInner s s := by
  classical
  simp_rw [fischerInner_X_mul_X_mul, ite_true]
  rw [Finset.sum_add_distrib, sum_fischerInner_pderiv_self hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma sum_fischerInner_divergence_X_mul (q : σ → MvPolynomial σ ℝ) :
    (∑ i : σ, fischerInner (q i) (X i * polynomialDivergence q)) =
      fischerInner (polynomialDivergence q) (polynomialDivergence q) := by
  simp_rw [← fischerInner_pderiv_left]
  rw [← fischerInner_sum_left]
  rfl

lemma sum_fischerInner_sub_C_mul_self (a : ℝ) (q : σ → MvPolynomial σ ℝ)
    (s : MvPolynomial σ ℝ) :
    (∑ i : σ, fischerInner (q i - C a * (X i * s)) (q i - C a * (X i * s))) =
      (∑ i : σ, fischerInner (q i) (q i)) -
      2 * a * (∑ i : σ, fischerInner (q i) (X i * s)) +
      a ^ 2 * (∑ i : σ, fischerInner (X i * s) (X i * s)) := by
  classical
  calc
    _ = ∑ i : σ, (fischerInner (q i) (q i) -
        2 * a * fischerInner (q i) (X i * s) +
        a ^ 2 * fischerInner (X i * s) (X i * s)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [fischerInner_sub_left, fischerInner_sub_right,
        fischerInner_C_mul_left, fischerInner_C_mul_right]
      rw [fischerInner_symm (X i * s) (q i)]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem fischerInner_divergence_self_le_of_nonempty [Nonempty σ] {k : ℕ}
    (hk : 1 ≤ k) (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) :
    fischerInner (polynomialDivergence q) (polynomialDivergence q) ≤
      ((k : ℝ) + (Fintype.card σ : ℝ) - 1) * ∑ i : σ, fischerInner (q i) (q i) := by
  classical
  let L : ℝ := (k : ℝ) + (Fintype.card σ : ℝ) - 1
  have hL : 0 < L := by
    have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
    have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp [L]
    linarith
  have hLn : L ≠ 0 := ne_of_gt hL
  have hcoeff : ((k - 1 : ℕ) : ℝ) + (Fintype.card σ : ℝ) = L := by
    rw [Nat.cast_sub hk]
    dsimp [L]
    push_cast
    ring
  have hnorm := sum_fischerInner_X_mul_self (polynomialDivergence_isHomogeneous q hq)
  rw [hcoeff] at hnorm
  have hpos : 0 ≤ ∑ i : σ,
      fischerInner (q i - C L⁻¹ * (X i * polynomialDivergence q))
        (q i - C L⁻¹ * (X i * polynomialDivergence q)) :=
    Finset.sum_nonneg fun i _ => fischerInner_self_nonneg _
  rw [sum_fischerInner_sub_C_mul_self, sum_fischerInner_divergence_X_mul, hnorm] at hpos
  have hidentity :
      (∑ i : σ, fischerInner (q i) (q i)) -
        2 * L⁻¹ * fischerInner (polynomialDivergence q) (polynomialDivergence q) +
        L⁻¹ ^ 2 * (L * fischerInner (polynomialDivergence q) (polynomialDivergence q)) =
      (∑ i : σ, fischerInner (q i) (q i)) -
        L⁻¹ * fischerInner (polynomialDivergence q) (polynomialDivergence q) := by
    field_simp [hLn]
    <;> ring
  rw [hidentity] at hpos
  have hmul := mul_nonneg (le_of_lt hL) hpos
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hLn, one_mul] at hmul
  change fischerInner (polynomialDivergence q) (polynomialDivergence q) ≤
    L * ∑ i : σ, fischerInner (q i) (q i)
  linarith

theorem fischerInner_divergence_self_le {k : ℕ} (hk : 1 ≤ k)
    (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).IsHomogeneous k) :
    fischerInner (polynomialDivergence q) (polynomialDivergence q) ≤
      ((k : ℝ) + (Fintype.card σ : ℝ) - 1) * ∑ i : σ, fischerInner (q i) (q i) := by
  cases isEmpty_or_nonempty σ with
  | inl h =>
    letI := h
    simp [polynomialDivergence, fischerInner_zero_left]
  | inr h =>
    letI := h
    exact fischerInner_divergence_self_le_of_nonempty hk q hq

end OAI.AnisotropicCalderon.AngularPolynomial

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_divergence_self_le
