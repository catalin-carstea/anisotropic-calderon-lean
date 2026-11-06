import Calderon.SphereSobolevBalancedDualEndpointKernel
import Calderon.SmoothKernelCodomainStructureTransport
import Calderon.SphereSobolevBalancedDualEndpointExtension
import Calderon.SphereSobolevCompatibleInterpolationTopology
import Calderon.ProdInheritedStructureData

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevBalancedDualCompatible_mem_iff (T : SphereSobolevBalancedDualEndpointPair) :
    T ∈ sphereSobolevBalancedDualCompatibleEndpoints ↔
      (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T.2 =
        T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  change
    (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T.2 -
      T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) = 0 ↔ _
  exact sub_eq_zero

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualCompatible_mem_iff
