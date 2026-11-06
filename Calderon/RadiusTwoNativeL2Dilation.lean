import Calderon.RadiusTwoNativeZeroDilationConstruction
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! EXPANSION.json precedes the genuine L2 class transport across the two balls. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem quasiMeasurePreserving_radiusTwo_comp_two :
    QuasiMeasurePreserving (fun x : R3 => (2 : ℝ) • x)
      ((volume : Measure R3).restrict ballOpens)
      ((volume : Measure R3).restrict radiusTwoOpens) := by
  apply (quasiMeasurePreserving_smul (μ := (volume : Measure R3)) (by norm_num : (2 : ℝ) ≠ 0)).restrict
  intro x hx
  change x ∈ Metric.ball (0 : R3) 1 at hx
  have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
  change (2 : ℝ) • x ∈ ball (0 : R3) 2
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
  norm_num
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem memLp_radiusTwo_L2_comp_two
    (f : Lp V 2 ((volume : Measure R3).restrict radiusTwoOpens)) :
    MemLp (fun x : R3 => f ((2 : ℝ) • x)) 2
      ((volume : Measure R3).restrict ballOpens) := by
  have hAE : AEStronglyMeasurable (fun x : R3 => f ((2 : ℝ) • x))
      ((volume : Measure R3).restrict ballOpens) :=
    (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
      quasiMeasurePreserving_radiusTwo_comp_two
  unfold MemLp
  exact lt_of_le_of_lt (eLpNorm_unit_comp_two_le_radiusTwo (f : R3 → V)) (Lp.memLp f).eLpNorm_lt_top

theorem norm_radiusTwo_L2_comp_two_le
    (f : Lp V 2 ((volume : Measure R3).restrict radiusTwoOpens)) :
    ‖(memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x))‖ ≤ ‖f‖ := by
  have ht := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_unit_comp_two_le_radiusTwo (f : R3 → V))
  rw [Lp.norm_def,eLpNorm_congr_ae (MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two f)),Lp.norm_def]
  exact ht

def radiusTwoNativeL2Dilation :
    Lp V 2 ((volume : Measure R3).restrict radiusTwoOpens) →L[ℝ]
      Lp V 2 ((volume : Measure R3).restrict ballOpens) := by
  let Q := quasiMeasurePreserving_radiusTwo_comp_two
  let D : Lp V 2 ((volume : Measure R3).restrict radiusTwoOpens) →ₗ[ℝ]
      Lp V 2 ((volume : Measure R3).restrict ballOpens) :=
    { toFun := fun f => (memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two (f+g)),
          MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two f),
          MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two g),
          Lp.coeFn_add
            ((memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x)))
            ((memLp_radiusTwo_L2_comp_two g).toLp (fun x : R3 => g ((2 : ℝ) • x))),
          Q.ae_eq_comp (Lp.coeFn_add f g)] with x hfg hf hg hAdd hComp
        change (f+g) ((2 : ℝ) • x) = f ((2 : ℝ) • x) + g ((2 : ℝ) • x) at hComp
        simpa only [Function.comp_apply,Pi.add_apply] using
          (hfg.trans hComp).trans ((hAdd.trans (congrArg₂ (fun r s : V => r+s) hf hg)).symm)
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two (c • f)),
          MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two f),
          Lp.coeFn_smul c ((memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x))),
          Q.ae_eq_comp (Lp.coeFn_smul c f)] with x hcf hf hSmul hComp
        change (c • f) ((2 : ℝ) • x) = c • f ((2 : ℝ) • x) at hComp
        simpa only [RingHom.id_apply,Function.comp_apply,Pi.smul_apply] using
          (hcf.trans hComp).trans ((hSmul.trans (congrArg (fun r : V => c • r) hf)).symm) }
  exact D.mkContinuous 1 (fun f => by
    change ‖(memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x))‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_radiusTwo_L2_comp_two_le f)

theorem radiusTwoNativeL2Dilation_apply_ae
    (f : Lp V 2 ((volume : Measure R3).restrict radiusTwoOpens)) :
    (radiusTwoNativeL2Dilation f : R3 → V)
      =ᵐ[(volume : Measure R3).restrict ballOpens] (fun x : R3 => f ((2 : ℝ) • x)) :=
  MemLp.coeFn_toLp (memLp_radiusTwo_L2_comp_two f)

theorem norm_radiusTwoNativeL2Dilation_le_one : ‖radiusTwoNativeL2Dilation (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(memLp_radiusTwo_L2_comp_two f).toLp (fun x : R3 => f ((2 : ℝ) • x))‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_radiusTwo_L2_comp_two_le f

end OAI.AnisotropicCalderon.ExteriorSource
