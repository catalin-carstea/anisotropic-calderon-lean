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
lemma norm_sphereSobolevBalancedDualMiddle_le
    (A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (T : sphereSobolevBalancedDualCompatibleEndpoints)
    (hT : T.val = ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B,
      (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A)) :
    ‖(sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).comp
        (sphereSobolevBalancedDualInterpolationL T)‖ ≤ max ‖A‖ ‖B‖ := by
  have hPost : ‖(sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).comp
      (sphereSobolevBalancedDualInterpolationL T)‖ ≤
      ‖sphereSobolevBalancedDualInterpolationL T‖ :=
    ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).opNorm_comp_le _).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _)
        (norm_nonneg _)).trans_eq (one_mul _))
  have hL : sphereSobolevBalancedDualInterpolationL T =
      sphereSobolevBalancedDualInterpolation T :=
    (sphereSobolevBalancedDualInterpolationL_apply T).trans
      (sphereSobolevBalancedDualInterpolation_eq_endpointL T).symm
  have hMiddle : ‖sphereSobolevBalancedDualInterpolationL T‖ ≤ ‖T‖ := by
    exact (congrArg
      (fun Q : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => ‖Q‖)
      hL).le.trans (norm_sphereSobolevBalancedDualInterpolation_le T)
  have hn : ‖(sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B‖ ≤ ‖B‖ :=
    ((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).opNorm_comp_le B).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _)
        (norm_nonneg _)).trans_eq (one_mul _))
  have hh : ‖(sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A‖ ≤ ‖A‖ :=
    ((sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).opNorm_comp_le A).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _)
        (norm_nonneg _)).trans_eq (one_mul _))
  have hPair : ‖T‖ ≤ max ‖A‖ ‖B‖ := by
    have hNorm : ‖T‖ = max ‖T.1.1‖ ‖T.1.2‖ := rfl
    have hPair := congrArg
      (fun Q : SphereSobolevBalancedDualEndpointPair => max ‖Q.1‖ ‖Q.2‖) hT
    exact hNorm.le.trans (hPair.le.trans
      (max_le (hn.trans (le_max_right _ _)) (hh.trans (le_max_left _ _))))
  exact hPost.trans (hMiddle.trans hPair)


end OAI.AnisotropicCalderon.SphereHarmonic
