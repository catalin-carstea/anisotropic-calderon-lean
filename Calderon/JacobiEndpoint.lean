import Calderon.JacobiSmall
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Set
namespace OAI.AnisotropicCalderon.JacobiIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "⟪" x "," y "⟫" => inner ℝ x y

theorem endpoint_pair_sub_norm_sq (j j' : ℝ → E) :
    ⟪j' 1,j 1⟫-⟪j' 0,j 0⟫-‖j 1-j 0‖^2 =
      ⟪j' 1-(j 1-j 0),j 1⟫-⟪j' 0-(j 1-j 0),j 0⟫ := by
  rw [← real_inner_self_eq_norm_sq (j 1-j 0)]
  simp only [inner_sub_left, inner_sub_right]
  ring

theorem abs_endpoint_pair_sub_norm_sq_le (j j' f : ℝ → E) (k : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k*‖j s‖) :
    |⟪j' 1,j 1⟫-⟪j' 0,j 0⟫-‖j 1-j 0‖^2| ≤
      2*k*(endpointSize j)^2 := by
  rw [endpoint_pair_sub_norm_sq]
  have hD1 := norm_small_solution_derivative_sub_endpoints_le j j' f 1 k
    (by norm_num) hj hj' hf hk hk1 hforce
  have hD0 := norm_small_solution_derivative_sub_endpoints_le j j' f 0 k
    (by norm_num) hj hj' hf hk hk1 hforce
  have hm : 0 ≤ endpointSize j := (norm_nonneg (j 0)).trans (le_max_left _ _)
  have hA : ‖j 1‖ ≤ endpointSize j := le_max_right _ _
  have hB : ‖j 0‖ ≤ endpointSize j := le_max_left _ _
  have h1 := (abs_real_inner_le_norm (j' 1-(j 1-j 0)) (j 1)).trans
    (mul_le_mul hD1 hA (norm_nonneg _) (mul_nonneg hk hm))
  have h0 := (abs_real_inner_le_norm (j' 0-(j 1-j 0)) (j 0)).trans
    (mul_le_mul hD0 hB (norm_nonneg _) (mul_nonneg hk hm))
  have h := norm_sub_le ⟪j' 1-(j 1-j 0),j 1⟫ ⟪j' 0-(j 1-j 0),j 0⟫
  simp only [Real.norm_eq_abs] at h
  nlinarith

#print axioms abs_endpoint_pair_sub_norm_sq_le
end OAI.AnisotropicCalderon.JacobiIntegral
