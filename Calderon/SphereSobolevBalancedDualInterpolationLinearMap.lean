import Calderon.SphereSobolevBalancedDualInterpolationAlgebra

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

def sphereSobolevBalancedDualInterpolationLinear :
    sphereSobolevBalancedDualCompatibleEndpoints →ₗ[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) where
  toFun := sphereSobolevBalancedDualInterpolation
  map_add' := sphereSobolevBalancedDualInterpolation_add
  map_smul' := sphereSobolevBalancedDualInterpolation_smul

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationLinear
