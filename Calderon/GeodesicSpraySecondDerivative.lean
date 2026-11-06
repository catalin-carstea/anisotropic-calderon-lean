import Calderon.GeodesicSprayLinearization
import Calderon.MixedFlowDerivatives

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fderiv_geodesicPhaseField_apply (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (p h : E × E) :
    fderiv ℝ (geodesicPhaseField Q M) p h =
      (h.2,-(fderiv ℝ (coordinateConnectionField Q M) p.1 h.1 p.2 p.2 +
        coordinateConnectionField Q M p.1 h.2 p.2 +
        coordinateConnectionField Q M p.1 p.2 h.2)) := by
  have hΓ := ((contDiff_coordinateConnectionField_infty Q M hQ hM).differentiable
    (by simp) p.1).hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hV := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt (x := p)
  have hR := (hΓ.clm_apply hV).clm_apply hV
  have hp := hV.prodMk hR.neg
  change HasFDerivAt (geodesicPhaseField Q M) _ p at hp
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.prod_apply,neg_apply,
    add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  congr 1
  change -(coordinateConnectionField Q M p.1 p.2 h.2 +
    (coordinateConnectionField Q M p.1 h.2 p.2 +
      fderiv ℝ (coordinateConnectionField Q M) p.1 h.1 p.2 p.2)) = _
  abel

theorem fderiv_fderiv_geodesicPhaseField_zero_velocity (Q M : E → E →L[ℝ] E)
    (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M) (y : E) (h k : E × E) :
    fderiv ℝ (fderiv ℝ (geodesicPhaseField Q M)) (y,0) k h =
      (0,-(coordinateConnectionField Q M y h.2 k.2 +
        coordinateConnectionField Q M y k.2 h.2)) := by
  let Γ := coordinateConnectionField Q M
  have hΓs : ContDiff ℝ ∞ Γ := contDiff_coordinateConnectionField_infty Q M hQ hM
  have hΓ := (hΓs.differentiable (by simp) y).hasFDerivAt.comp
    (y,(0 : E)) (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hV := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt (x := (y,(0 : E)))
  have hDGs : ContDiff ℝ ∞ (fun z : E × E => fderiv ℝ Γ z.1 h.1) :=
    ((hΓs.fderiv_right (by simp)).comp contDiff_fst).clm_apply contDiff_const
  have hT1 := (((hDGs.differentiable (by simp) (y,0)).hasFDerivAt.clm_apply hV).clm_apply hV)
  have hT10 : HasFDerivAt
      (fun z : E × E => fderiv ℝ Γ z.1 h.1 z.2 z.2)
      (0 : (E × E) →L[ℝ] E) (y,0) := by simpa using hT1
  have hconst : HasFDerivAt (fun _ : E × E => h.2) (0 : (E × E) →L[ℝ] E) (y,0) :=
    hasFDerivAt_const _ _
  have hT2 := (hΓ.clm_apply hconst).clm_apply hV
  have hT3 := (hΓ.clm_apply hV).clm_apply hconst
  have hp := hconst.prodMk ((hT10.add hT2).add hT3).neg
  change HasFDerivAt (fun z : E × E =>
    (h.2,-(fderiv ℝ Γ z.1 h.1 z.2 z.2 + Γ z.1 h.2 z.2 + Γ z.1 z.2 h.2))) _ (y,0) at hp
  have he : (fun z => fderiv ℝ (geodesicPhaseField Q M) z h) =
      (fun z : E × E => (h.2,-(fderiv ℝ Γ z.1 h.1 z.2 z.2 +
        Γ z.1 h.2 z.2 + Γ z.1 z.2 h.2))) := by
    funext z
    exact fderiv_geodesicPhaseField_apply Q M hQ hM z h
  rw [← fderiv_fderiv_apply_const _ (contDiff_geodesicPhaseField Q M hQ hM) (y,0) h k,
    he,hp.fderiv]
  simp [Γ]
end OAI.AnisotropicCalderon.ConnectionError
