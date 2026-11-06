import Calderon.RadiusTwoSmoothValueMultiplier

/-! Full EXPANSION.json precedes actual bounded smooth coefficient multiplication. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem exists_radiusTwo_smoothValueMultiplier (χ : SmoothData) :
    ∃ L : RadiusTwoL2 →L[ℝ] RadiusTwoL2, ∀ f : RadiusTwoL2,
      (L f : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun x => χ.1 x * f x) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) 2).bddAbove_image
    χ.2.continuous.norm.continuousOn
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |χ.1 x| ≤ max C 0 := by
    intro x hx
    have hxB : x ∈ closedBall (0 : R3) 2 := ball_subset_closedBall hx
    have hCx : ‖χ.1 x‖ ≤ C := hC ⟨x,hxB,rfl⟩
    simpa only [Real.norm_eq_abs] using le_trans hCx (le_max_left C 0)
  exact ⟨radiusTwoSmoothValueMultiplierL χ hM hAbs,
    fun f => radiusTwoSmoothValueMultiplierL_apply_ae χ hM hAbs f⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_smoothValueMultiplier
