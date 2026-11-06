import Calderon.SphereSobolevBalancedDualInterpolationLinearMap
import Calderon.SphereSobolevBalancedDualInterpolationValueBound

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma dist_sphereSobolevBalancedDualInterpolation_le
    (T S : sphereSobolevBalancedDualCompatibleEndpoints) :
    dist (sphereSobolevBalancedDualInterpolation T) (sphereSobolevBalancedDualInterpolation S) ≤
      dist (T : SphereSobolevBalancedDualEndpointPair) (S : SphereSobolevBalancedDualEndpointPair) := by
  have hsub : sphereSobolevBalancedDualInterpolation (T-S) =
      sphereSobolevBalancedDualInterpolation T - sphereSobolevBalancedDualInterpolation S :=
    map_sub sphereSobolevBalancedDualInterpolationLinear T S
  calc
    _ = ‖sphereSobolevBalancedDualInterpolation T - sphereSobolevBalancedDualInterpolation S‖ :=
      sphereInterpolation_clm_dist_eq_norm _ _
    _ = ‖sphereSobolevBalancedDualInterpolation (T-S)‖ := congrArg norm hsub.symm
    _ ≤ ‖T-S‖ := norm_sphereSobolevBalancedDualInterpolation_le (T-S)
    _ = _ := (sphereInterpolation_pair_clm_dist_eq_norm T.1 S.1).symm

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.dist_sphereSobolevBalancedDualInterpolation_le
