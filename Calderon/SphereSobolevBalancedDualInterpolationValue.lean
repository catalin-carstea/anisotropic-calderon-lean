import Calderon.SphereSobolevBalancedDualEndpointCompatibility

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

def sphereSobolevBalancedDualInterpolation (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereSobolevBalancedDualEndpointL T.1.1 T.1.2
    (sphereSobolevBalancedDualCompatible_inclusion_comp_eq T)

lemma sphereSobolevBalancedDualInterpolation_eq_endpointL
    (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    sphereSobolevBalancedDualInterpolation T =
      sphereSobolevBalancedDualEndpointL T.1.1 T.1.2
        ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2) := rfl

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolation
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolation_eq_endpointL
