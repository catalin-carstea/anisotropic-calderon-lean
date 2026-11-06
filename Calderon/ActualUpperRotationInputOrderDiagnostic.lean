import Calderon.SphereSobolevOrderOneRotation

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SmoothSphereRotationProjection

/-! Actual map values, not equality of erased-order carriers, are compared component by component. -/
lemma sphereSobolevRotationL_upper_rotation_input_order_diagnostic (i j : Fin 3) :
    sphereSobolevRotationL ((3/2:ℝ)+1) i j = sphereSobolevRotationL (5/2:ℝ) i j := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k) =
    (1+(k:ℝ))⁻¹ • harmonicSphereRotation k i j (u k)
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevRotationL_upper_rotation_input_order_diagnostic
