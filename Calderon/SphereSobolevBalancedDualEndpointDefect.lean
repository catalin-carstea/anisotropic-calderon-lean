import Calderon.SphereSobolevBalancedDualEndpointPair
import Calderon.SphereSobolevCompatibleInterpolationTopology

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereSobolevBalancedDualEndpointDefectL : SphereSobolevBalancedDualEndpointPair →L[ℝ]
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ))) :=
  sphereInterpolationEndpointDefectL
    (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualEndpointDefectL
