import Calderon.QradFourIndexPivotIdentity

/-! Finite real tensor norm-square fold. Exact conditional domain premises retained. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma real_inner_weighted_matrix_sums {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Q : Fin 3 → Fin 3 → ℝ) (A B : Fin 3 → Fin 3 → V) :
    ⟪∑ i, ∑ j, Q i j • A i j, ∑ k, ∑ l, Q k l • B k l⟫_ℝ =
      ∑ i, ∑ j, ∑ k, ∑ l, Q i j * Q k l * ⟪A i j,B k l⟫_ℝ := by
  calc
    _ = ∑ i, ∑ j, ⟪Q i j • A i j, ∑ k, ∑ l, Q k l • B k l⟫_ℝ := by
      simp only [sum_inner]
    _ = _ := by
      simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring

lemma norm_cubic_weighted_matrix_sum_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Q : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → Fin 3 → V)
    (radius : ℝ) :
    ‖radius^3 • ∑ i, ∑ j, Q i j • A i j‖^2 =
      radius^6 * ∑ i, ∑ j, ∑ k, ∑ l, Q i j * Q k l * ⟪A i j,A k l⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
    real_inner_weighted_matrix_sums]
  ring

lemma tensor_gram_difference_eq_cubic_norm_difference {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : Fin 3 → Fin 3 → ℝ) (A B : Fin 3 → Fin 3 → V)
    (W : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hW : ∀ i j k l, W i j k l = ⟪A i j,A k l⟫_ℝ - ⟪B i j,B k l⟫_ℝ)
    (radius : ℝ) :
    radius^6 * (∑ i, ∑ j, ∑ k, ∑ l, Q i j * Q k l * W i j k l) =
      ‖radius^3 • ∑ i, ∑ j, Q i j • A i j‖^2 -
        ‖radius^3 • ∑ i, ∑ j, Q i j • B i j‖^2 := by
  simp_rw [hW, mul_sub, Finset.sum_sub_distrib]
  rw [mul_sub, norm_cubic_weighted_matrix_sum_sq, norm_cubic_weighted_matrix_sum_sq]

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JH" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "ZH" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "P" => sphereSobolevDualPairing (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevDualPairing qradFourIndexWeakForm

variable (RH LH : Fin 3 → Hi →L[ℝ] Half) (RL LL : Fin 3 → Half →L[ℝ] Neg)
  (CH : Fin 3 → Fin 3 → Hi →L[ℝ] Half) (CL : Fin 3 → Fin 3 → Half →L[ℝ] Neg)
  (hR : ∀ i v, JH (RH i v) = RL i (IH v))
  (hL : ∀ i v, JH (LH i v) = LL i (IH v))
  (hC : ∀ i k v, JH (CH i k v) = CL i k (IH v))
  (hBracket : ∀ i k v, CL i k (IH v) = LL i (RH k v) - RL k (LH i v))
  (hLAdj : ∀ i (z : Half) (v : Hi), P (LL i z) (IH v) = ⟪ZH z,ZH (RH i v)⟫_ℝ)
  (hRAdj : ∀ i (z : Half) (v : Hi), P (RL i z) (IH v) = ⟪ZH z,ZH (LH i v)⟫_ℝ)


include hR hL hC hBracket hLAdj hRAdj in
theorem qradSignedWeakSelfExpression_eq_cubic_norm_difference
    (Q : Fin 3 → Fin 3 → ℝ) (radius : ℝ) (u : Hi)
    (r l : Fin 3 → Hi) (hr : ∀ i, IH (r i) = RH i u)
    (hl : ∀ i, IH (l i) = LH i u) :
    qradSignedWeakSelfExpression RH LH LL CH CL Q radius u =
      ‖radius^3 • ∑ i, ∑ j, Q i j • ZH (RH i (r j))‖^2 -
        ‖radius^3 • ∑ i, ∑ j, Q i j • ZH (LH j (l i))‖^2 := by
  unfold qradSignedWeakSelfExpression
  exact tensor_gram_difference_eq_cubic_norm_difference Q
    (fun i j => ZH (RH i (r j))) (fun i j => ZH (LH j (l i)))
    (fun i j k s => qradFourIndexWeakForm RH LH LL CH CL i j k s u)
    (fun i j k s => qradFourIndexWeakForm_eq_second_output_gram_difference
      RH LH RL LL CH CL hR hL hC hBracket hLAdj hRAdj u r l hr hl i j k s) radius

end OAI.AnisotropicCalderon.SphereHarmonic
