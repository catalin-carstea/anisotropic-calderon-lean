import Calderon.SphereSobolevBalancedDualInterpolationValue

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma sphereSobolevBalancedDualInterpolation_lower_inclusion_apply
    (T : sphereSobolevBalancedDualCompatibleEndpoints) (u : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
      (sphereSobolevBalancedDualInterpolation T u) =
    T.1.1 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u) :=
  congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)) => A u)
    (sphereSobolevBalancedDualEndpointL_lower_inclusion T.1.1 T.1.2
      ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolation_lower_inclusion_apply
