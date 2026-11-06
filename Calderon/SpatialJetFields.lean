import Calderon.BoundedParameterSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Function Set
open scoped BoundedContinuousFunction ContDiff
universe u
namespace OAI.AnisotropicCalderon.SpatialJetFields

variable {H V E : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialJetField (j : ℕ) (g : H × V → E) (z : H × V) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => V) E :=
  (iteratedFDeriv ℝ j g z).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ H V)

theorem contDiff_spatial_slice (g : H × V → E) (hg : ContDiff ℝ ∞ g) (t : H) :
    ContDiff ℝ ∞ (fun x => g (t,x)) :=
  hg.comp (contDiff_const.prodMk contDiff_id)

theorem spatialJetField_eq_iteratedFDeriv (j : ℕ) (g : H × V → E)
    (hg : ContDiff ℝ ∞ g) (t : H) (x : V) :
    spatialJetField j g (t,x) = iteratedFDeriv ℝ j (fun y => g (t,y)) x := by
  have hc : ContDiff ℝ ∞ (fun z : H × V => g ((t,0) + z)) :=
    hg.comp (contDiff_const.add contDiff_id)
  have he : (fun y : V => g (t,y)) =
      (fun z : H × V => g ((t,0) + z)) ∘ ContinuousLinearMap.inr ℝ H V := by
    funext y
    simp
  rw [he,(ContinuousLinearMap.inr ℝ H V).iteratedFDeriv_comp_right hc x (by simp)]
  rw [iteratedFDeriv_comp_add_left]
  simp [spatialJetField]

theorem contDiff_spatialJetField (j : ℕ) (g : H × V → E) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spatialJetField j g) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j => ContinuousLinearMap.inr ℝ H V))).comp
        (hg.iteratedFDeriv_right (m := ∞) (by simp))

theorem tsupport_spatial_slice_subset (g : H × V → E) (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) :
    tsupport (fun x => g (t,x)) ⊆ K := by
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra h
  exact hx (hz t x h)

theorem hasCompactSupport_spatial_slice (g : H × V → E) (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) :
    HasCompactSupport (fun x => g (t,x)) :=
  hK.of_isClosed_subset isClosed_closure (tsupport_spatial_slice_subset g K hK hz t)

theorem spatialJetField_zero_outside (j : ℕ) (g : H × V → E)
    (hg : ContDiff ℝ ∞ g) (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ∀ t x, x ∉ K → spatialJetField j g (t,x) = 0 := by
  intro t x hx
  rw [spatialJetField_eq_iteratedFDeriv j g hg t x]
  by_contra hs
  exact hx (tsupport_spatial_slice_subset g K hK hz t
    (support_iteratedFDeriv_subset (𝕜 := ℝ) j hs))

theorem contDiff_infty_spatialJetSlice (j : ℕ) (g : H × V → E)
    (hg : ContDiff ℝ ∞ g) (K : Set V) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (CommonSupportSlices.commonSupportSlice
      (spatialJetField j g) (contDiff_spatialJetField j g hg).continuous K hK
      (spatialJetField_zero_outside j g hg K hK hz)) :=
  BoundedParameterSmoothness.contDiff_infty_commonSupportSlice _
    (contDiff_spatialJetField j g hg) K hK (spatialJetField_zero_outside j g hg K hK hz)

end OAI.AnisotropicCalderon.SpatialJetFields
