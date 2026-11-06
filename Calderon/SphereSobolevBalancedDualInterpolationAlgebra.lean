import Calderon.SphereSobolevBalancedDualInterpolationEvaluation

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic
open DirichletFamily.DriftBootstrap

lemma sphereSobolevBalancedDualInterpolation_add
    (T S : sphereSobolevBalancedDualCompatibleEndpoints) :
    sphereSobolevBalancedDualInterpolation (T+S) =
      sphereSobolevBalancedDualInterpolation T + sphereSobolevBalancedDualInterpolation S := by
  apply ContinuousLinearMap.ext
  intro u
  let J := sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
  let v := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u
  have hT : J (sphereSobolevBalancedDualInterpolation T u) = T.1.1 v :=
    sphereSobolevBalancedDualInterpolation_lower_inclusion_apply T u
  have hS : J (sphereSobolevBalancedDualInterpolation S u) = S.1.1 v :=
    sphereSobolevBalancedDualInterpolation_lower_inclusion_apply S u
  have hTS : J (sphereSobolevBalancedDualInterpolation (T+S) u) = T.1.1 v + S.1.1 v :=
    sphereSobolevBalancedDualInterpolation_lower_inclusion_apply (T+S) u
  have hadd : J (sphereSobolevBalancedDualInterpolation T u + sphereSobolevBalancedDualInterpolation S u) =
      T.1.1 v + S.1.1 v :=
    (J.map_add _ _).trans (congrArg₂ (fun x y : SphereSobolev (-(3/2 : ℝ)) => x+y) hT hS)
  exact sphereSobolevInclusionL_injective (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
    (hTS.trans hadd.symm)

lemma sphereSobolevBalancedDualInterpolation_smul
    (c : ℝ) (T : sphereSobolevBalancedDualCompatibleEndpoints) :
    sphereSobolevBalancedDualInterpolation (c • T) = c • sphereSobolevBalancedDualInterpolation T := by
  apply ContinuousLinearMap.ext
  intro u
  let J := sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
  let v := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u
  have hT : J (sphereSobolevBalancedDualInterpolation T u) = T.1.1 v :=
    sphereSobolevBalancedDualInterpolation_lower_inclusion_apply T u
  have hct : J (sphereSobolevBalancedDualInterpolation (c • T) u) = c • T.1.1 v :=
    sphereSobolevBalancedDualInterpolation_lower_inclusion_apply (c • T) u
  have hc : J (c • sphereSobolevBalancedDualInterpolation T u) = c • T.1.1 v :=
    (J.map_smul c _).trans (congrArg (fun x : SphereSobolev (-(3/2 : ℝ)) => c • x) hT)
  exact sphereSobolevInclusionL_injective (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
    (hct.trans hc.symm)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolation_add
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualInterpolation_smul
