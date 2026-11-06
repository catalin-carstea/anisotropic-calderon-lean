import Calderon.SphereSobolevBalancedDualInterpolationValue

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma norm_sphereSobolevBalancedDualInterpolation_le
    (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    ‖sphereSobolevBalancedDualInterpolation T‖ ≤ ‖T‖ := by
  calc
    _ ≤ (‖T.1.1‖ + ‖T.1.2‖) / 2 :=
      norm_sphereSobolevBalancedDualEndpointL_le T.1.1 T.1.2
        ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2)
    _ ≤ ‖T‖ := by
      change (‖T.1.1‖ + ‖T.1.2‖) / 2 ≤ max ‖T.1.1‖ ‖T.1.2‖
      linarith [le_max_left ‖T.1.1‖ ‖T.1.2‖,le_max_right ‖T.1.1‖ ‖T.1.2‖]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevBalancedDualInterpolation_le
