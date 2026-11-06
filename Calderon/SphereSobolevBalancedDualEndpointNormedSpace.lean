import Calderon.SphereSobolevBalancedDualEndpointMembership

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic

@[instance_reducible, instance] def sphereSobolevBalancedDualCompatibleNormedSpace :
    NormedSpace ℝ sphereSobolevBalancedDualCompatibleEndpoints where
  toModule := sphereSobolevBalancedDualCompatibleEndpoints.module
  norm_smul_le c T := by
    change max ‖c • T.1.1‖ ‖c • T.1.2‖ ≤ ‖c‖ * max ‖T.1.1‖ ‖T.1.2‖
    apply max_le
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))
    · exact (ContinuousLinearMap.opNorm_smul_le c T.1.2).trans
        (mul_le_mul_of_nonneg_left (le_max_right ‖T.1.1‖ ‖T.1.2‖) (norm_nonneg c))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualCompatibleNormedSpace
