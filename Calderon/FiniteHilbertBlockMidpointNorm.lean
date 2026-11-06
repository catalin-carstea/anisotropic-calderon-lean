import Calderon.FiniteHilbertBlockMidpoint

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SpectralSylvester

variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]

lemma finite_lp_midpoint_output_square_bound
    (T0 T1 : lp E 2 →L[ℝ] lp E 2) (s : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ k ∈ s, 0 < r k)
    (hc : ∀ i ∈ s, ∀ j ∈ s, ∀ z : E j,
      (T1 (lp.single (E := E) 2 j z)) i =
        ((r i)^2/(r j)^2) • (T0 (lp.single (E := E) 2 j z)) i)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hT0 : ‖T0‖ ≤ M0) (hT1 : ‖T1‖ ≤ M1)
    (u : ∀ k, E k) :
    (∑ i ∈ s, ‖∑ j ∈ s, (r i/r j) • (T0 (lp.single (E := E) 2 j (u j))) i‖^2) ≤
      ((M0+M1)/2)^2 * ∑ j ∈ s, ‖u j‖^2 := by
  let w : ∀ i, E i := fun i => ∑ j ∈ s, (r i/r j) • (T0 (lp.single (E := E) 2 j (u j))) i
  let A : ℝ := ∑ i ∈ s, ‖w i‖^2
  let B : ℝ := ∑ j ∈ s, ‖u j‖^2
  let C : ℝ := (M0+M1)/2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : (∑ i ∈ s, ∑ j ∈ s,
      (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (u j))) i,w i⟫_ℝ) = A := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← real_inner_self_eq_norm_sq]
    change (∑ j ∈ s, (r i/r j)*⟪(T0 (lp.single (E := E) 2 j (u j))) i,w i⟫_ℝ) =
      ⟪∑ j ∈ s, (r i/r j) • (T0 (lp.single (E := E) 2 j (u j))) i,w i⟫_ℝ
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    exact (real_inner_smul_left _ _ _).symm
  have h := finite_lp_midpoint_block_bound T0 T1 s r hr hc M0 M1 hM0 hM1 hT0 hT1 u w
  rw [he,abs_of_nonneg hA] at h
  change A ≤ C*Real.sqrt B*Real.sqrt A at h
  have hAsq := Real.sq_sqrt hA
  have hBsq := Real.sq_sqrt hB
  have hCB : 0 ≤ C*Real.sqrt B := mul_nonneg hC (Real.sqrt_nonneg _)
  have hs : Real.sqrt A ≤ C*Real.sqrt B := by
    nlinarith [Real.sqrt_nonneg A]
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg A) hs
  have hCBsq : (C*Real.sqrt B)^2 = C^2*B := by rw [mul_pow,hBsq]
  change A ≤ C^2*B
  nlinarith

end OAI.AnisotropicCalderon.SpectralSylvester
