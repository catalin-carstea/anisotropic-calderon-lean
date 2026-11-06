import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-! Elementary real-pivot cancellation, with no operator or domain premise. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma real_inner_difference_sum_eq_norm_sq_sub
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) :
    ⟪x-y,x⟫_ℝ + ⟪x-y,y⟫_ℝ = ‖x‖^2 - ‖y‖^2 := by
  have hxx := real_inner_self_eq_norm_sq (F := V) x
  have hyy := real_inner_self_eq_norm_sq (F := V) y
  have hxy := real_inner_comm x y
  rw [inner_sub_left,inner_sub_left]
  linarith

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.real_inner_difference_sum_eq_norm_sq_sub
