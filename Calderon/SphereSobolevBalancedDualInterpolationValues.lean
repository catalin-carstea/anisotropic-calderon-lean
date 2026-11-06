import Calderon.SphereSobolevBalancedDualInterpolationDistance

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma lipschitzWith_sphereSobolevBalancedDualInterpolation :
    LipschitzWith 1 sphereSobolevBalancedDualInterpolation :=
  sphereInterpolation_subtype_clm_lipschitz
    (V := SphereSobolevBalancedDualEndpointPair)
    (W := SphereSobolev (1/2 : ℝ)) (Z := SphereSobolev (-(1/2 : ℝ)))
    (sphereSobolevBalancedDualCompatibleEndpoints : Set SphereSobolevBalancedDualEndpointPair)
    sphereSobolevBalancedDualInterpolation dist_sphereSobolevBalancedDualInterpolation_le

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.lipschitzWith_sphereSobolevBalancedDualInterpolation
