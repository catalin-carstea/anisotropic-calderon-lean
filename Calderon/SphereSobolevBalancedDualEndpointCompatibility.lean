import Calderon.SphereSobolevBalancedDualEndpointStructure

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma sphereSobolevBalancedDualCompatible_inclusion_comp_eq
    (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T.1.2 =
      T.1.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) :=
  ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualCompatible_inclusion_comp_eq
