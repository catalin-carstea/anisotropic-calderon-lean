import Calderon.SmoothFlowLinearization

set_option autoImplicit false
noncomputable section
open scoped ContDiff NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def flowBaseVariation (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (h : E) (p : E × ℝ) : E :=
  fderiv ℝ (fun q : E × ℝ => ODE.globalSolution v hv q.1 q.2) p (h,0)

def flowSecondBaseVariation (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (h k : E) (p : E × ℝ) : E := fderiv ℝ (flowBaseVariation v hv h) p (k,0)

theorem contDiff_flowBaseVariation (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (h : E) :
    ContDiff ℝ ∞ (flowBaseVariation v hv h) :=
  ((contDiff_infty_globalSolution v hv hvs).fderiv_right (by simp)).clm_apply contDiff_const

theorem flowBaseVariation_zero (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a h : E) :
    flowBaseVariation v hv h (a,0) = h := by
  rw [flowBaseVariation,← fderiv_base_slice _ (contDiff_infty_globalSolution v hv hvs) a h 0]
  simp only [ODE.globalSolution_zero]
  exact congrArg (fun L : E →L[ℝ] E => L h) (hasFDerivAt_id a).fderiv

theorem flowSecondBaseVariation_zero (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a h k : E) :
    flowSecondBaseVariation v hv h k (a,0) = 0 := by
  rw [flowSecondBaseVariation,← fderiv_base_slice _ (contDiff_flowBaseVariation v hv hvs h) a k 0]
  have he : (fun x => flowBaseVariation v hv h (x,0)) = (fun _ : E => h) := by
    funext x
    exact flowBaseVariation_zero v hv hvs x h
  rw [he]
  simp

theorem fderiv_flowBaseVariation_time (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a h : E) (t : ℝ) :
    fderiv ℝ (flowBaseVariation v hv h) (a,t) (0,1) =
      fderiv ℝ v (ODE.globalSolution v hv a t) (flowBaseVariation v hv h (a,t)) := by
  have hd := ((contDiff_flowBaseVariation v hv hvs h).differentiable
    (by simp) (a,t)).hasFDerivAt.comp_hasDerivAt t
    ((show HasDerivAt (fun _ : ℝ => a) 0 t from hasDerivAt_const _ _).prodMk
      (hasDerivAt_id t))
  exact hd.unique (hasDerivAt_globalSolution_baseDerivative v hv hvs a h t)

theorem hasDerivAt_flowSecondBaseVariation (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a h k : E) (t : ℝ) :
    HasDerivAt (fun s => flowSecondBaseVariation v hv h k (a,s))
      (fderiv ℝ v (ODE.globalSolution v hv a t) (flowSecondBaseVariation v hv h k (a,t)) +
        fderiv ℝ (fderiv ℝ v) (ODE.globalSolution v hv a t)
          (flowBaseVariation v hv k (a,t)) (flowBaseVariation v hv h (a,t))) t := by
  let F : E × ℝ → E := fun p => ODE.globalSolution v hv p.1 p.2
  let J := flowBaseVariation v hv h
  have hF : ContDiff ℝ ∞ F := contDiff_infty_globalSolution v hv hvs
  have hJ : ContDiff ℝ ∞ J := contDiff_flowBaseVariation v hv hvs h
  have hmix := hasDerivAt_base_derivative_in_time J hJ a k t
  have he : (fun x => fderiv ℝ J (x,t) (0,1)) =
      (fun x => fderiv ℝ v (F (x,t)) (J (x,t))) := by
    funext x
    exact fderiv_flowBaseVariation_time v hv hvs x h t
  rw [he] at hmix
  have hFs : DifferentiableAt ℝ (fun x => F (x,t)) a :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) a
  have hJs : DifferentiableAt ℝ (fun x => J (x,t)) a :=
    (hJ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) a
  have hvsD : ContDiff ℝ ∞ (fderiv ℝ v) := hvs.fderiv_right (by simp)
  have hD := (hvsD.differentiable
    (by simp) (F (a,t))).hasFDerivAt.comp a hFs.hasFDerivAt
  have hp := hD.clm_apply hJs.hasFDerivAt
  simp only [Function.comp_def] at hp
  have hvalue : fderiv ℝ (fun x => fderiv ℝ v (F (x,t)) (J (x,t))) a k =
      fderiv ℝ v (F (a,t)) (flowSecondBaseVariation v hv h k (a,t)) +
        fderiv ℝ (fderiv ℝ v) (F (a,t))
          (flowBaseVariation v hv k (a,t)) (J (a,t)) := by
    rw [hp.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,fderiv_base_slice F hF a k t,
      fderiv_base_slice J hJ a k t]
    rfl
  exact hmix.congr_deriv hvalue
end OAI.AnisotropicCalderon.ConnectionError
