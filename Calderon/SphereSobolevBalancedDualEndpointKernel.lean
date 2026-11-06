import Calderon.SphereSobolevBalancedDualEndpointDefect

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic

def sphereSobolevBalancedDualCompatibleEndpoints :
    Submodule ℝ SphereSobolevBalancedDualEndpointPair :=
  sphereSobolevBalancedDualEndpointDefectL.ker

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualCompatibleEndpoints
