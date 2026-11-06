import Calderon.SphereSobolevPairing
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
lemma sphereSobolevDualPairing_half_add_sub
    (f : SphereSobolev (1/2:ℝ)) (a b c : SphereSobolev (-(1/2:ℝ))) :
    sphereSobolevDualPairing (1/2:ℝ) f (a+b-c) =
      sphereSobolevDualPairing (1/2:ℝ) f a +
      sphereSobolevDualPairing (1/2:ℝ) f b - sphereSobolevDualPairing (1/2:ℝ) f c := by
  change ⟪f,a+b-c⟫_ℝ=⟪f,a⟫_ℝ+⟪f,b⟫_ℝ-⟪f,c⟫_ℝ
  rw [inner_sub_right,inner_add_right]
end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevDualPairing_half_add_sub
