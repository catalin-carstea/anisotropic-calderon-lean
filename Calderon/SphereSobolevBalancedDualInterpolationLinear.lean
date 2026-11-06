import Calderon.SphereSobolevBalancedDualInterpolationValues
import Calderon.SphereSobolevBalancedDualInterpolationNorm

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

attribute [local instance] sphereSobolevBalancedDualInterpolationOperatorNorm

def sphereSobolevBalancedDualInterpolationL :
    sphereSobolevBalancedDualCompatibleEndpoints →L[ℝ]
      (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) where
  toLinearMap := sphereSobolevBalancedDualInterpolationLinear
  cont := lipschitzWith_sphereSobolevBalancedDualInterpolation.continuous

lemma sphereSobolevBalancedDualInterpolationL_apply (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    sphereSobolevBalancedDualInterpolationL T =
      sphereSobolevBalancedDualEndpointL T.1.1 T.1.2
        ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2) := rfl

lemma norm_sphereSobolevBalancedDualInterpolationL_le :
    ‖sphereSobolevBalancedDualInterpolationL‖ ≤ 1 := by
  have hBound := ContinuousLinearMap.opNorm_le_bound
    (E := sphereSobolevBalancedDualCompatibleEndpoints)
    (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) (σ₁₂ := RingHom.id ℝ)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    sphereSobolevBalancedDualCompatibleNormedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hBound
  apply hBound sphereSobolevBalancedDualInterpolationL zero_le_one
  intro T
  change ‖sphereSobolevBalancedDualInterpolation T‖ ≤ 1 * ‖T‖
  simpa only [one_mul] using norm_sphereSobolevBalancedDualInterpolation_le T

lemma sphereSobolevBalancedDualInterpolationL_lower_inclusion
    (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevBalancedDualInterpolationL T) =
    T.1.1.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) :=
  sphereSobolevBalancedDualEndpointL_lower_inclusion T.1.1 T.1.2
    ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2)

lemma sphereSobolevBalancedDualInterpolationL_upper_inclusion
    (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    (sphereSobolevBalancedDualInterpolationL T).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) =
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp T.1.2 :=
  sphereSobolevBalancedDualEndpointL_upper_inclusion T.1.1 T.1.2
    ((sphereSobolevBalancedDualCompatible_mem_iff T.1).mp T.2)

lemma contDiff_sphereSobolevBalancedDualInterpolationL :
    ContDiff ℝ ∞ (sphereSobolevBalancedDualInterpolationL :
      sphereSobolevBalancedDualCompatibleEndpoints →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) := by
  have hg := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := sphereSobolevBalancedDualCompatibleEndpoints)
    (F := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) (n := ∞)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    sphereSobolevBalancedDualCompatibleNormedSpace_module_eq] at hg
  exact hg sphereSobolevBalancedDualInterpolationL

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationL_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevBalancedDualInterpolationL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationL_lower_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolationL_upper_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_sphereSobolevBalancedDualInterpolationL
