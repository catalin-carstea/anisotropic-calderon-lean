import Calderon.NilpotentSecondVariation
import Calderon.GeodesicSpraySecondDerivative

set_option autoImplicit false
noncomputable section
open scoped ContDiff NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fderiv_flow_endpoint_apply (v : E × E → E × E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (x h : E × E) (t : ℝ) :
    fderiv ℝ (fun z => (ODE.globalSolution v hv z t).1) x h =
      (flowBaseVariation v hv h (x,t)).1 := by
  let F : (E × E) × ℝ → E × E := fun p => ODE.globalSolution v hv p.1 p.2
  have hF : ContDiff ℝ ∞ F := contDiff_infty_globalSolution v hv hvs
  have hs : DifferentiableAt ℝ (fun z => F (z,t)) x :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
  have hp := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp x hs.hasFDerivAt
  change HasFDerivAt (fun z => (ODE.globalSolution v hv z t).1) _ x at hp
  rw [hp.fderiv,ContinuousLinearMap.comp_apply,fderiv_base_slice F hF x h t]
  rfl

theorem fderiv_fderiv_flow_endpoint_apply (v : E × E → E × E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (x h k : E × E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => (ODE.globalSolution v hv z t).1)) x k h =
      (flowSecondBaseVariation v hv h k (x,t)).1 := by
  have hs : ContDiff ℝ ∞ (fun z => (ODE.globalSolution v hv z t).1) :=
    contDiff_fst.comp ((contDiff_infty_globalSolution v hv hvs).comp
      (contDiff_id.prodMk contDiff_const))
  rw [← fderiv_fderiv_apply_const _ hs x h k]
  have he : (fun z => fderiv ℝ (fun q => (ODE.globalSolution v hv q t).1) z h) =
      (fun z => (flowBaseVariation v hv h (z,t)).1) := by
    funext z
    exact fderiv_flow_endpoint_apply v hv hvs z h t
  rw [he]
  let J := flowBaseVariation v hv h
  have hJ : ContDiff ℝ ∞ J := contDiff_flowBaseVariation v hv hvs h
  have hj : DifferentiableAt ℝ (fun z => J (z,t)) x :=
    (hJ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
  have hp := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp x hj.hasFDerivAt
  change HasFDerivAt (fun z => (flowBaseVariation v hv h (z,t)).1) _ x at hp
  rw [hp.fderiv,ContinuousLinearMap.comp_apply,fderiv_base_slice J hJ x k t]
  rfl

theorem fderiv_fderiv_stationary_spray_endpoint (v : E × E → E × E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (y : E)
    (hz : v (y,0) = 0) (hD : fderiv ℝ v (y,0) = zeroVelocityLinearization)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hH : ∀ h k : E × E, fderiv ℝ (fderiv ℝ v) (y,0) k h =
      (0,-(Γ h.2 k.2 + Γ k.2 h.2))) (h k : E × E) :
    fderiv ℝ (fderiv ℝ (fun z => (ODE.globalSolution v hv z 1).1)) (y,0) k h =
      -(1/2 : ℝ) • (Γ h.2 k.2 + Γ k.2 h.2) := by
  let C : E × E := (0,-(Γ h.2 k.2 + Γ k.2 h.2))
  have hn (d : E × E) : fderiv ℝ v (y,0) (fderiv ℝ v (y,0) d) = 0 := by
    rw [hD]
    exact zeroVelocityLinearization_nilpotent d
  have hf (t : ℝ) : fderiv ℝ (fderiv ℝ v) (y,0)
      (k + t • fderiv ℝ v (y,0) k) (h + t • fderiv ℝ v (y,0) h) = C := by
    rw [hH,hD]
    simp [C,zeroVelocityLinearization_apply]
  have hw := globalSolution_secondBaseVariation_nilpotent v hv hvs (y,0) hz hn h k C hf 1
  rw [fderiv_fderiv_flow_endpoint_apply v hv hvs (y,0) h k 1]
  simpa [C,hD,zeroVelocityLinearization_apply,smul_neg,neg_smul,add_comm] using congrArg Prod.fst hw
end OAI.AnisotropicCalderon.ConnectionError
