import Calderon.MemLpDilationContinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem tendsto_eLpNorm_inward_dilation_sub_of_memLp_ball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (hf : MemLp f 2 ((volume : Measure R3).restrict ballOpens)) :
    Tendsto (fun a : ℝ => eLpNorm (fun x : R3 => f (a • x) - f x) 2
      ((volume : Measure R3).restrict ballOpens)) (𝓝[<] 1) (𝓝 0) := by
  let F : R3 → V := (ballOpens : Set R3).indicator f
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have hF : MemLp F 2 (volume : Measure R3) :=
    (memLp_indicator_iff_restrict hB.nullMeasurableSet).mpr hf
  have hLim : Tendsto
      (fun a : ℝ => eLpNorm (fun x : R3 => F (a • x) - F x) 2 volume)
      (𝓝[<] 1) (𝓝 0) :=
    (tendsto_eLpNorm_dilation_sub_of_memLp F hF).mono_left nhdsWithin_le_nhds
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have haPos : ∀ᶠ a : ℝ in 𝓝[<] 1, 0 < a :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [haPos,self_mem_nhdsWithin,
    ENNReal.tendsto_nhds_zero.mp hLim ε hε] with a ha0 ha1 hSmall
  have ha1' : a < 1 := ha1
  have hEq : (fun x : R3 => f (a • x) - f x)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x : R3 => F (a • x) - F x) := by
    filter_upwards [ae_restrict_mem hB] with x hx
    have hxNorm : ‖x‖ < 1 := by
      simpa only [coe_ballOpens,B,mem_ball,dist_zero_right] using hx
    have hax : a • x ∈ (ballOpens : Set R3) := by
      change a • x ∈ ball (0 : R3) 1
      rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
      calc
        a * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ha1'.le (norm_nonneg x)
        _ < 1 := by simpa only [one_mul] using hxNorm
    simp only [F,indicator_of_mem hx,indicator_of_mem hax]
  calc
    eLpNorm (fun x : R3 => f (a • x) - f x) 2
        ((volume : Measure R3).restrict ballOpens)
      = eLpNorm (fun x : R3 => F (a • x) - F x) 2
          ((volume : Measure R3).restrict ballOpens) := eLpNorm_congr_ae hEq
    _ ≤ eLpNorm (fun x : R3 => F (a • x) - F x) 2 volume :=
      eLpNorm_restrict_le _ _ _ _
    _ ≤ ε := hSmall

end OAI.AnisotropicCalderon.DirichletFamily
