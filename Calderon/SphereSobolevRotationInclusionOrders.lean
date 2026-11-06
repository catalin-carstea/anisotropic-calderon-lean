import Calderon.SphereSobolevInclusion
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma sphereSobolevInclusionL_threehalf_rotation_orders :
    sphereSobolevInclusionL ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num) =
      sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num) := by
  have hDelta : ((1/2:ℝ)-1)-((3/2:ℝ)-1) = (-1/2:ℝ)-(1/2:ℝ) := by norm_num
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  have hLeft := sphereSobolevInclusionL_apply ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num) u k
  have hRight := sphereSobolevInclusionL_apply (1/2:ℝ) (-1/2:ℝ) (by norm_num) u k
  exact hLeft.trans ((congrArg (fun r : ℝ => besselWeight r k • u k) hDelta).trans hRight.symm)

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_threehalf_rotation_orders
