import Calderon.SphereSobolevCompletion
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
/-! Equality of actual real orders,
eliminated generically before specializing numeric/actual-family parameters. -/
lemma sphereSobolevSingleL_eq_of_order_eq
    (s t : ℝ) (hst : s=t) (k : ℕ) (u : harmonicSphereSubspace k) :
    sphereSobolevSingleL s k u = sphereSobolevSingleL t k u := by
  cases hst
  rfl
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevSingleL_eq_of_order_eq
end OAI.AnisotropicCalderon.SphereHarmonic
