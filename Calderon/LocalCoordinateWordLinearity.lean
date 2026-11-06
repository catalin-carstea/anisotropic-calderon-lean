import Calderon.ActualReferenceLocalCoordinateWordJets
import Calderon.ActualReferenceDDHigherHCoframeJets
import Calderon.FiniteDimensionalLocalSmoothExtension
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ReferenceDensityBounds

lemma coordinateFieldWordPartial_const_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (c : ℝ) (f : R3 → E) :
    coordinateFieldWordPartial w (fun y => c • f y) =
      fun y => c • coordinateFieldWordPartial w f y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
      change (fun x => fderiv ℝ (coordinateFieldWordPartial w (fun y => c • f y)) x
        (coordinateDirection k)) =
        fun x => c • fderiv ℝ (coordinateFieldWordPartial w f) x (coordinateDirection k)
      rw [ih]
      funext x
      have hScalar := congrFun
        (fderiv_const_smul_field (𝕜 := ℝ) (f := coordinateFieldWordPartial w f) c) x
      simpa only [Pi.smul_def, Pi.smul_apply, ContinuousLinearMap.smul_apply] using
        congrArg (fun A : R3 →L[ℝ] E => A (coordinateDirection k)) hScalar

lemma coordinateFieldWordPartial_sum_of_isOpen {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (F : ι → R3 → E) (U : Set R3)
    (hU : IsOpen U) (hF : ∀ i : ι, ContDiffOn ℝ ∞ (F i) U)
    (x : R3) (hx : x ∈ U) :
    coordinateFieldWordPartial w (fun y => ∑ i : ι, F i y) x =
      ∑ i : ι, coordinateFieldWordPartial w (F i) x := by
  classical
  have hExt : ∀ i : ι, ∃ F₀ : R3 → E, ContDiff ℝ ∞ F₀ ∧ F₀ =ᶠ[𝓝 x] F i := by
    intro i
    obtain ⟨F₀, hSmooth, _, hNear⟩ :=
      DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
        ({x} : Set R3) U isCompact_singleton hU
        (by simpa only [singleton_subset_iff] using hx) (F i) (hF i)
    exact ⟨F₀, hSmooth, hNear x (by simp)⟩
  choose F₀ hSmooth hNear using hExt
  have hSumNear : (fun y => ∑ i : ι, F₀ i y) =ᶠ[𝓝 x] (fun y => ∑ i : ι, F i y) := by
    filter_upwards [Filter.eventually_all.mpr hNear] with y hy
    exact Finset.sum_congr rfl (fun i _ => hy i)
  have hGlobal := coordinateFieldWordPartial_sum w F₀ hSmooth
  calc
    coordinateFieldWordPartial w (fun y => ∑ i : ι, F i y) x =
        coordinateFieldWordPartial w (fun y => ∑ i : ι, F₀ i y) x :=
      (coordinateFieldWordPartial_eventuallyEq w hSumNear).eq_of_nhds.symm
    _ = ∑ i : ι, coordinateFieldWordPartial w (F₀ i) x := congrFun hGlobal x
    _ = ∑ i : ι, coordinateFieldWordPartial w (F i) x :=
      Finset.sum_congr rfl (fun i _ =>
        (coordinateFieldWordPartial_eventuallyEq w (hNear i)).eq_of_nhds)

end OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets

#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.coordinateFieldWordPartial_const_smul
#print axioms OAI.AnisotropicCalderon.ActualReferenceLocalCoordinateWordJets.coordinateFieldWordPartial_sum_of_isOpen
