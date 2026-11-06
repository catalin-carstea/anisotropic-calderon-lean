import Calderon.RadiusTwoNativeTestDilation
import Calderon.LpDilationScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Full EXPANSION.json precedes this focused partition of original nativezero dilation5. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal Distributions ContDiff Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem eLpNorm_unit_comp_two_le_radiusTwo
    {V : Type*} [NormedAddCommGroup V] (f : R3 → V) :
    eLpNorm (fun x : R3 => f ((2 : ℝ) • x)) 2
      ((volume : Measure R3).restrict ballOpens) ≤
        eLpNorm f 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
  let F : R3 → V := (radiusTwoOpens : Set R3).indicator f
  have he : (fun x : R3 => f ((2 : ℝ) • x))
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x : R3 => F ((2 : ℝ) • x)) := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    change x ∈ Metric.ball (0 : R3) 1 at hx
    have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    have htwo : (2 : ℝ) • x ∈ (radiusTwoOpens : Set R3) := by
      change (2 : ℝ) • x ∈ ball (0 : R3) 2
      rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
      norm_num
      linarith
    simp only [F,indicator_of_mem htwo]
  have hScale : eLpNorm (fun x : R3 => F ((2 : ℝ) • x)) 2 (volume : Measure R3) =
      ENNReal.ofReal ((1/2 : ℝ) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) *
        eLpNorm F 2 (volume : Measure R3) := by
    simpa only [one_div,inv_inv] using
      eLpNorm_comp_inv_smul_R3 F (show 0 < (1/2 : ℝ) by norm_num) 2
  have hfactor : ENNReal.ofReal
      ((1/2 : ℝ) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) ≤ 1 := by
    have hr : ((1/2 : ℝ) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
    simpa using ENNReal.ofReal_le_ofReal hr
  calc
    eLpNorm (fun x : R3 => f ((2 : ℝ) • x)) 2
        ((volume : Measure R3).restrict ballOpens) =
      eLpNorm (fun x : R3 => F ((2 : ℝ) • x)) 2
        ((volume : Measure R3).restrict ballOpens) := eLpNorm_congr_ae he
    _ ≤ eLpNorm (fun x : R3 => F ((2 : ℝ) • x)) 2 (volume : Measure R3) :=
      eLpNorm_restrict_le _ _ _ _
    _ = ENNReal.ofReal ((1/2 : ℝ) ^
        ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) *
        eLpNorm F 2 (volume : Measure R3) := hScale
    _ ≤ 1 * eLpNorm F 2 (volume : Measure R3) := mul_le_mul' hfactor le_rfl
    _ = eLpNorm f 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
      rw [one_mul,eLpNorm_indicator_eq_eLpNorm_restrict
        radiusTwoOpens.isOpen.measurableSet.nullMeasurableSet]

end OAI.AnisotropicCalderon.ExteriorSource
