import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.DirichletFamily

lemma inv_smul_moving_taylor_sub_first_order
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r f : ℝ) (c d t a b k l dr tr : V) (hr : r ≠ 0) :
    r⁻¹ • ((r⁻¹ • (c + r • d + r^2 • t) + r • (a + r • b + r^2 • k) +
      f • (l + r • dr + r^2 • tr)) -
      (r⁻¹ • c + f • l + (d + (r*f) • dr))) =
    t + a + r • b + r^2 • k + (r*f) • tr := by
  match_scalars <;> field_simp [hr] <;> ring

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.inv_smul_moving_taylor_sub_first_order
