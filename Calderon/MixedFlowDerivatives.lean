import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {X G E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_apply_const (F : X → G) (hF : ContDiff ℝ ∞ F)
    (p d e : X) :
    fderiv ℝ (fun x => fderiv ℝ F x d) p e =
      fderiv ℝ (fderiv ℝ F) p e d := by
  let L : (X →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G d
  have hD : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  have h := L.hasFDerivAt.comp p hD.hasFDerivAt
  exact congrArg (fun A : X →L[ℝ] G => A e) h.fderiv

theorem hasDerivAt_base_derivative_in_time (F : E × ℝ → G)
    (hF : ContDiff ℝ ∞ F) (a h : E) (t : ℝ) :
    HasDerivAt (fun s => fderiv ℝ F (a,s) (h,0))
      (fderiv ℝ (fun x => fderiv ℝ F (x,t) (0,1)) a h) t := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  let L : ((E × ℝ) →L[ℝ] G) →L[ℝ] G :=
    ContinuousLinearMap.apply ℝ G (h,0)
  have htime := (L.hasFDerivAt.comp (a,t)
    (hD.differentiable (by simp) (a,t)).hasFDerivAt).comp_hasDerivAt t
    ((show HasDerivAt (fun _ : ℝ => a) 0 t from hasDerivAt_const _ _).prodMk
      (hasDerivAt_id t))
  have hslice : HasFDerivAt (fun x : E => (x,t))
      (ContinuousLinearMap.inl ℝ E ℝ) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const t a)
  let T : ((E × ℝ) →L[ℝ] G) →L[ℝ] G :=
    ContinuousLinearMap.apply ℝ G (0,1)
  have hbase : DifferentiableAt ℝ (fun p : E × ℝ => fderiv ℝ F p (0,1)) (a,t) :=
    T.differentiableAt.comp (a,t) (hD.differentiable (by simp) (a,t))
  have heq : fderiv ℝ (fun x => fderiv ℝ F (x,t) (0,1)) a h =
      fderiv ℝ (fderiv ℝ F) (a,t) (h,0) (0,1) := by
    change fderiv ℝ ((fun p : E × ℝ => fderiv ℝ F p (0,1)) ∘
      (fun x => (x,t))) a h = _
    rw [fderiv_comp a hbase hslice.differentiableAt, hslice.fderiv]
    exact fderiv_fderiv_apply_const F hF (a,t) (0,1) (h,0)
  rw [heq]
  have hsym : IsSymmSndFDerivAt ℝ F (a,t) :=
    hF.contDiffAt.isSymmSndFDerivAt (by simp)
  have ht : HasDerivAt (fun s => fderiv ℝ F (a,s) (h,0))
      (fderiv ℝ (fderiv ℝ F) (a,t) (0,1) (h,0)) t := by
    simpa only [L, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using htime
  exact ht.congr_deriv (hsym (0,1) (h,0))

end OAI.AnisotropicCalderon.ConnectionError
