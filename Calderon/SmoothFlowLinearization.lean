import Calderon.SmoothGeodesicFlow
import Calderon.MixedFlowDerivatives

set_option autoImplicit false
noncomputable section
open scoped ContDiff NNReal
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_base_slice (F : E × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (a h : E) (t : ℝ) :
    fderiv ℝ (fun x => F (x,t)) a h = fderiv ℝ F (a,t) (h,0) := by
  have hs : HasFDerivAt (fun x : E => (x,t))
      (ContinuousLinearMap.inl ℝ E ℝ) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const t a)
  have hc := (hF.differentiable (by simp) (a,t)).hasFDerivAt.comp a hs
  exact congrArg (fun A : E →L[ℝ] E => A h) hc.fderiv

variable [CompleteSpace E]

theorem fderiv_globalSolution_time (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (x : E) (t : ℝ) :
    fderiv ℝ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2)
      (x,t) (0,1) = v (ODE.globalSolution v hv x t) := by
  have hF := contDiff_infty_globalSolution v hv hvs
  have hd := (hF.differentiable (by simp) (x,t)).hasFDerivAt.comp_hasDerivAt t
    ((show HasDerivAt (fun _ : ℝ => x) 0 t from hasDerivAt_const _ _).prodMk
      (hasDerivAt_id t))
  exact hd.unique (ODE.hasDerivAt_globalSolution v hv x t)

theorem hasDerivAt_globalSolution_baseDerivative (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a h : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ
      (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) (a,s) (h,0))
      (fderiv ℝ v (ODE.globalSolution v hv a t)
        (fderiv ℝ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) (a,t) (h,0))) t := by
  let F : E × ℝ → E := fun p => ODE.globalSolution v hv p.1 p.2
  have hF : ContDiff ℝ ∞ F := contDiff_infty_globalSolution v hv hvs
  have hmix := hasDerivAt_base_derivative_in_time F hF a h t
  have heq : (fun x => fderiv ℝ F (x,t) (0,1)) =
      (fun x => v (ODE.globalSolution v hv x t)) := by
    funext x
    exact fderiv_globalSolution_time v hv hvs x t
  rw [heq] at hmix
  have hs : DifferentiableAt ℝ (fun x => F (x,t)) a :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) a
  have hc := (hvs.differentiable (by simp) (F (a,t))).hasFDerivAt.comp a hs.hasFDerivAt
  have hj : fderiv ℝ (fun x => v (F (x,t))) a h =
      fderiv ℝ v (F (a,t)) (fderiv ℝ F (a,t) (h,0)) := by
    change fderiv ℝ (v ∘ (fun x => F (x,t))) a h = _
    rw [hc.fderiv, ContinuousLinearMap.comp_apply, fderiv_base_slice F hF a h t]
  exact hmix.congr_deriv hj

theorem globalSolution_baseDerivative_nilpotent (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvs : ContDiff ℝ ∞ v) (a : E) (ha : v a = 0)
    (hnil : ∀ h, fderiv ℝ v a (fderiv ℝ v a h) = 0) (h : E) (t : ℝ) :
    fderiv ℝ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2)
      (a,t) (h,0) = h + t • fderiv ℝ v a h := by
  let L : E →L[ℝ] E := fderiv ℝ v a
  let J : ℝ → E := fun s => fderiv ℝ
    (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2) (a,s) (h,0)
  have hJ : ∀ s, HasDerivAt J (L (J s)) s := by
    intro s
    have hd := hasDerivAt_globalSolution_baseDerivative v hv hvs a h s
    simpa only [globalSolution_stationary v hv a ha, J, L] using hd
  have hJ0 : J 0 = h := by
    change fderiv ℝ (fun p : E × ℝ => ODE.globalSolution v hv p.1 p.2)
      (a,0) (h,0) = h
    rw [← fderiv_base_slice _ (contDiff_infty_globalSolution v hv hvs) a h 0]
    simp only [ODE.globalSolution_zero]
    exact congrArg (fun A : E →L[ℝ] E => A h) (hasFDerivAt_id a).fderiv
  have hC : ∀ s, HasDerivAt (fun r : ℝ => h + r • L h)
      (L (h + s • L h)) s := by
    intro s
    have hLnil : L (L h) = 0 := hnil h
    simpa only [map_add, map_smul, hLnil, smul_zero, add_zero, one_smul, id_eq] using
      (hasDerivAt_id s).smul_const (L h) |>.const_add h
  have hj := ODE.eq_globalSolution L L.lipschitzWith hJ
  have hcurve := ODE.eq_globalSolution L L.lipschitzWith hC
  rw [hJ0] at hj
  simp only [zero_smul, add_zero] at hcurve
  exact congrFun (hj.trans hcurve.symm) t

end OAI.AnisotropicCalderon.ConnectionError
