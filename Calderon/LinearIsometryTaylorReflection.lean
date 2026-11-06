import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.LinearIsometryTaylorReflection
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem hasFDerivWithinAt_of_linearIsometry_comp
    (e : F →ₗᵢ[ℝ] G) (f : E → F) (f' : E →L[ℝ] F) (s : Set E) (x : E)
    (h : HasFDerivWithinAt (e ∘ f) (e.toContinuousLinearMap.comp f') s x) :
    HasFDerivWithinAt f f' s x := by
  apply HasFDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_norm_left
  have hn := h.isLittleO.norm_left
  have he (y : E) :
      ‖(e ∘ f) y-(e ∘ f) x-(e.toContinuousLinearMap.comp f') (y-x)‖ =
      ‖f y-f x-f' (y-x)‖ := by
    change ‖e (f y)-e (f x)-e (f' (y-x))‖ = _
    rw [← map_sub,← map_sub,e.norm_map]
  simpa only [he] using hn

def multilinearPostcompositionIsometry (e : F →ₗᵢ[ℝ] G) (m : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F →ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin m => E) G :=
  ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin m => E) F G e.toContinuousLinearMap).toLinearMap,
    fun A => e.norm_compContinuousMultilinearMap A⟩

theorem hasFTaylorSeriesUpToOn_of_linearIsometry_comp
    (e : F →ₗᵢ[ℝ] G) (n : ℕ∞ω) (f : E → F)
    (p : E → FormalMultilinearSeries ℝ E F) (s : Set E)
    (h : HasFTaylorSeriesUpToOn n (e ∘ f)
      (fun x m => e.toContinuousLinearMap.compContinuousMultilinearMap (p x m)) s) :
    HasFTaylorSeriesUpToOn n f p s := by
  constructor
  · intro x hx
    apply e.injective
    exact h.zero_eq x hx
  · intro m hm x hx
    let I := multilinearPostcompositionIsometry (E := E) e m
    apply hasFDerivWithinAt_of_linearIsometry_comp I (fun y => p y m)
      (p x m.succ).curryLeft s x
    exact h.fderivWithin m hm x hx
  · intro m hm
    let I := multilinearPostcompositionIsometry (E := E) e m
    apply I.isometry.comp_continuousOn_iff.mp
    exact h.cont m hm

end OAI.AnisotropicCalderon.LinearIsometryTaylorReflection
