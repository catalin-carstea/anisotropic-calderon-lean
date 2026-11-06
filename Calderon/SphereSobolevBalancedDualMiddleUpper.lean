import Calderon.SphereSobolevBalancedDualInterpolationLinear
import Calderon.SphereSobolevBalancedDualInterpolationValueBound
import Calderon.SphereSobolevBalancedDualEndpointStructure
import Calderon.SphereSobolevBesselOrderCompatibility
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL
lemma sphereSobolevBalancedDualMiddle_upper
    (A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (T : sphereSobolevBalancedDualCompatibleEndpoints)
    (hT : T.val = ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B,
      (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A))
    (u : SphereSobolev (3/2 : ℝ)) :
    ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).comp
        (sphereSobolevBalancedDualInterpolationL T))
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (A u) := by
  have h := DFunLike.congr_fun (sphereSobolevBalancedDualInterpolationL_upper_inclusion T) u
  simp only [ContinuousLinearMap.comp_apply] at h
  have h2 : T.val.2 = (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A :=
    congrArg Prod.snd hT
  have hBupper := DFunLike.congr_fun
    (sphereSobolevBesselOrderL_inclusion_comp (3/2 : ℝ) (1/2 : ℝ)
      (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (A u)
  simp only [ContinuousLinearMap.comp_apply] at hBupper
  have hInv := DFunLike.congr_fun (sphereSobolevBesselOrderL_inverse (1/2 : ℝ) (-(1/2 : ℝ)))
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (A u))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hInv
  have h2u := DFunLike.congr_fun h2 u
  simp only [ContinuousLinearMap.comp_apply] at h2u
  have hStep := h.trans (congrArg
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) h2u)
  simp only [ContinuousLinearMap.comp_apply]
  exact (congrArg (sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ))
    (hStep.trans hBupper)).trans hInv

end OAI.AnisotropicCalderon.SphereHarmonic
