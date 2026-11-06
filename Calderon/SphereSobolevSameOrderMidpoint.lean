import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.SphereSobolevCompatibleEndpointInterpolation

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

variable (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
  (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
  (hc : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp H =
    L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))

def sphereSobolevSameOrderEndpoints : sphereSobolevCompatibleEndpoints :=
  ⟨((sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp L,
      (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)).comp H), by
    change (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      ((sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)).comp H) =
      ((sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp L).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    have hB := sphereSobolevBesselOrderL_inclusion_comp
      (3/2:ℝ) (1/2:ℝ) (1/2:ℝ) (-1/2:ℝ) (by norm_num) (by norm_num) (by norm_num)
    calc
      _ = ((sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
          (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))).comp H := rfl
      _ = ((sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))).comp H :=
        congrArg (fun A => A.comp H) hB
      _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp
          ((sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp H) := rfl
      _ = (sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp
          (L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :=
        congrArg (fun A => (sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp A) hc
      _ = _ := rfl⟩

def sphereSobolevSameOrderMidpointL : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  (sphereSobolevBesselOrderL 0 1).comp
    (sphereSobolevCompatibleMidpointL (sphereSobolevSameOrderEndpoints L H hc))

lemma sphereSobolevSameOrderMidpointL_lower_inclusion :
    (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp
      (sphereSobolevSameOrderMidpointL L H hc) =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let T := sphereSobolevSameOrderEndpoints L H hc
  let J : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevCompatibleMidpointL T
  apply ContinuousLinearMap.ext
  intro u
  have hLower : sphereSobolevInclusionL 0 (-1/2:ℝ) (by norm_num) (J u) =
      sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)
        (L (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-1/2:ℝ) => A u)
      (sphereSobolevCompatibleMidpointL_lower_inclusion T)
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  have hk := congrArg (sphereSobolevCoefficientL (-1/2:ℝ) k) hLower
  simp only [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_besselOrder] at hk
  have hw : (1/2:ℝ)-(-1/2:ℝ)=1 := by norm_num
  rw [hw] at hk
  have hPoint : sphereSobolevSameOrderMidpointL L H hc u = sphereSobolevBesselOrderL 0 1 (J u) := rfl
  have hInput := sphereSobolevCoefficientL_inclusion 1 (1/2:ℝ) (by norm_num)
    (sphereSobolevSameOrderMidpointL L H hc u) k
  have hB : sphereSobolevCoefficientL 1 k (sphereSobolevBesselOrderL 0 1 (J u)) =
      besselWeight (-1) k • sphereSobolevCoefficientL 0 k (J u) := by
    simpa only [zero_sub] using sphereSobolevCoefficientL_besselOrder 0 1 (J u) k
  have hCancel (a : harmonicSphereSubspace k) :
      besselWeight (-1) k • (besselWeight 1 k • a) = a := by
    rw [smul_smul,besselWeight_neg_mul_self,one_smul]
  exact hInput.trans ((congrArg (sphereSobolevCoefficientL 1 k) hPoint).trans
    (hB.trans ((congrArg (fun a : harmonicSphereSubspace k => besselWeight (-1) k • a) hk).trans
      (hCancel _))))

lemma sphereSobolevSameOrderMidpointL_upper_inclusion :
    (sphereSobolevSameOrderMidpointL L H hc).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).comp H := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 (1/2:ℝ) (by norm_num)
  have hLower := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (1/2:ℝ) =>
      A (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
    (sphereSobolevSameOrderMidpointL_lower_inclusion L H hc)
  have hIn := sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num)
  have hInU := congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A u) hIn
  have hInH := congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A (H u)) hIn
  have hCo := congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A u) hc
  simp only [ContinuousLinearMap.comp_apply] at hLower hInU hInH hCo ⊢
  exact hLower.trans ((congrArg L hInU).trans (hCo.symm.trans hInH.symm))

lemma norm_sphereSobolevSameOrderMidpointL_le :
    ‖sphereSobolevSameOrderMidpointL L H hc‖ ≤ max ‖L‖ ‖H‖ := by
  let T := sphereSobolevSameOrderEndpoints L H hc
  have hL : ‖(sphereSobolevBesselOrderL (1/2:ℝ) (-1/2:ℝ)).comp L‖ ≤ ‖L‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) L.opNorm_nonneg).trans_eq (one_mul _))
  have hH : ‖(sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ)).comp H‖ ≤ ‖H‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) H.opNorm_nonneg).trans_eq (one_mul _))
  have hT : ‖T‖ ≤ max ‖L‖ ‖H‖ :=
    max_le (hL.trans (le_max_left _ _)) (hH.trans (le_max_right _ _))
  calc
    _ ≤ ‖sphereSobolevBesselOrderL 0 1‖ * ‖sphereSobolevCompatibleMidpointL T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖sphereSobolevCompatibleMidpointL T‖ :=
      mul_le_mul_of_nonneg_right (norm_sphereSobolevBesselOrderL_le _ _) (sphereSobolevCompatibleMidpointL T).opNorm_nonneg
    _ = ‖sphereSobolevCompatibleMidpointL T‖ := one_mul _
    _ ≤ ‖T‖ := norm_sphereSobolevCompatibleMidpoint_le T
    _ ≤ max ‖L‖ ‖H‖ := hT

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevSameOrderEndpoints
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevSameOrderMidpointL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevSameOrderMidpointL_lower_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevSameOrderMidpointL_upper_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevSameOrderMidpointL_le
