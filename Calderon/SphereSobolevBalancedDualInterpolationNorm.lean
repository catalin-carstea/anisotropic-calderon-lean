import Calderon.SphereSobolevBalancedDualEndpointStructure

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

@[instance_reducible, local instance] def sphereSobolevBalancedDualInterpolationOperatorNorm :
    Norm (sphereSobolevBalancedDualCompatibleEndpoints →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) where
  norm A := ContinuousLinearMap.opNorm
    (E := sphereSobolevBalancedDualCompatibleEndpoints)
    (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (σ₁₂ := RingHom.id ℝ) A

lemma sphereSobolevBalancedDualInterpolationOperatorNorm_norm_def
    (A : sphereSobolevBalancedDualCompatibleEndpoints →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) :
    @Norm.norm _ sphereSobolevBalancedDualInterpolationOperatorNorm A =
      ContinuousLinearMap.opNorm
        (E := sphereSobolevBalancedDualCompatibleEndpoints)
        (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
        (σ₁₂ := RingHom.id ℝ) A := rfl

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationOperatorNorm
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationOperatorNorm_norm_def
