import Calderon.ActualMiddleSourceMatchedCutoff
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth

/-- All positive derivative orders use the very same first-derivative
support; no new cutoff or source region is selected. -/
theorem tsupport_iteratedFDeriv_succ_subset_fderiv
    (chi : R3 → ℝ) (n : ℕ) :
    tsupport (iteratedFDeriv ℝ (n+1) chi) ⊆ tsupport (fderiv ℝ chi) := by
  have hSub : Function.support (iteratedFDeriv ℝ (n+1) chi) ⊆
      tsupport (fderiv ℝ chi) := by
    intro x hx
    by_contra hNot
    have hz : iteratedFDeriv ℝ n (fderiv ℝ chi) x = 0 := by
      by_contra hn
      exact hNot (support_iteratedFDeriv_subset n hn)
    have hZero : iteratedFDeriv ℝ (n+1) chi x = 0 := by
      ext v
      rw [iteratedFDeriv_succ_apply_right,hz]
      rfl
    exact hx hZero
  exact closure_minimal hSub (isClosed_tsupport (fderiv ℝ chi))

/-- A single fixed open neighborhood contains supports of ALL positive
cutoff derivatives, with its closure strictly in the two actual source regions.
The assumptions are exactly the checked proper-cutoff geometry. -/
theorem exists_actual_cutoff_all_derivative_source_room
    (L tb : ℝ) (chi : R3 → ℝ) (hCompact : HasCompactSupport chi)
    (hSupport : tsupport chi ⊆ interior cylinder)
    (hDeriv : tsupport (fderiv ℝ chi) ⊆
      {z : R3 | z 2 < -(1/4 : ℝ)} ∪ {z : R3 | tb < referenceDepth L z}) :
    ∃ U : Set R3, IsOpen U ∧ tsupport (fderiv ℝ chi) ⊆ U ∧
      closure U ⊆ interior cylinder ∩
        ({z : R3 | z 2 < -(1/4 : ℝ)} ∪ {z : R3 | tb < referenceDepth L z}) ∧
      ∀ n : ℕ, tsupport (iteratedFDeriv ℝ (n+1) chi) ⊆ U := by
  let E : Set R3 := tsupport (fderiv ℝ chi)
  let V : Set R3 := interior cylinder ∩
    ({z : R3 | z 2 < -(1/4 : ℝ)} ∪ {z : R3 | tb < referenceDepth L z})
  have hE : IsCompact E := (hCompact.fderiv ℝ).isCompact
  have hV : IsOpen V := isOpen_interior.inter
    ((isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const).union
      (isOpen_lt continuous_const (contDiff_referenceDepth L).continuous))
  have hEV : E ⊆ V := fun x hx => ⟨hSupport (tsupport_fderiv_subset ℝ hx),hDeriv hx⟩
  obtain ⟨sigma,hsigma,hRoom⟩ := hE.exists_cthickening_subset_open hV hEV
  let U : Set R3 := thickening (sigma/2) E
  have hHalf : 0 < sigma/2 := by positivity
  have hHalfLe : sigma/2 ≤ sigma := by linarith
  have hEU : E ⊆ U := self_subset_thickening hHalf E
  refine ⟨U,isOpen_thickening,hEU,?_,?_⟩
  · exact (closure_thickening_subset_cthickening (sigma/2) E).trans
      ((cthickening_mono hHalfLe E).trans hRoom)
  · intro n
    exact (tsupport_iteratedFDeriv_succ_subset_fderiv chi n).trans hEU

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
