import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic

@[inline, reducible] def SphereSobolevBalancedDualEndpointPair :=
  (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(3/2 : ℝ))) ×
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))


end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.SphereSobolevBalancedDualEndpointPair
