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
lemma sphereSobolevBalancedDualMiddle_lower
    (A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (T : sphereSobolevBalancedDualCompatibleEndpoints)
    (hT : T.val = ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B,
      (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A))
    (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).comp
          (sphereSobolevBalancedDualInterpolationL T)) v) =
      B (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v) := by
  have h := DFunLike.congr_fun (sphereSobolevBalancedDualInterpolationL_lower_inclusion T) v
  simp only [ContinuousLinearMap.comp_apply] at h
  have h1 : T.val.1 = (sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B :=
    congrArg Prod.fst hT
  have h1v := DFunLike.congr_fun h1
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)
  simp only [ContinuousLinearMap.comp_apply] at h1v
  have hGraph := h.trans h1v
  have hBmBi := DFunLike.congr_fun (sphereSobolevBesselOrderL_inverse (-(1/2 : ℝ)) (1/2 : ℝ))
    (sphereSobolevBalancedDualInterpolationL T v)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hBmBi
  have hBlower := DFunLike.congr_fun
    (sphereSobolevBesselOrderL_inclusion_comp (1/2 : ℝ) (-(1/2 : ℝ))
      (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
    (sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)
      (sphereSobolevBalancedDualInterpolationL T v))
  simp only [ContinuousLinearMap.comp_apply] at hBlower
  have hStep := hBlower.symm.trans ((congrArg
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)) hBmBi).trans hGraph)
  have hBni (w : SphereSobolev (-(1/2 : ℝ))) :
      sphereSobolevBesselOrderL (-(3/2 : ℝ)) (-(1/2 : ℝ))
        (sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ)) w) = w := by
    have hw := DFunLike.congr_fun
      (sphereSobolevBesselOrderL_inverse (-(1/2 : ℝ)) (-(3/2 : ℝ))) w
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hw
  have hPulled := congrArg
    (sphereSobolevBesselOrderL (-(3/2 : ℝ)) (-(1/2 : ℝ))) hStep
  simp only [ContinuousLinearMap.comp_apply]
  exact (hBni _).symm.trans (hPulled.trans (hBni _))

end OAI.AnisotropicCalderon.SphereHarmonic
