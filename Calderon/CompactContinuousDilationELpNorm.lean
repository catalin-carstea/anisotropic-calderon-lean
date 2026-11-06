import Calderon.CompactContinuousDilationL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem tendsto_eLpNorm_dilation_sub_of_continuous_compactSupport
    {V : Type*} [NormedAddCommGroup V]
    (g : R3 → V) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun a : ℝ => eLpNorm (fun x : R3 => g (a • x) - g x) 2 volume)
      (𝓝 1) (𝓝 0) := by
  have hI := tendsto_integral_norm_sq_dilation_sub_of_continuous_compactSupport g hg hgc
  have hRoot := hI.rpow_const (Or.inr (show (0 : ℝ) ≤ 1/2 by norm_num))
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hRoot
  have ht : Tendsto (fun a : ℝ => ENNReal.ofReal
      ((∫ x : R3, ‖g (a • x) - g x‖^2) ^ (1/2 : ℝ))) (𝓝 1) (𝓝 0) := by
    simpa [Function.comp_def] using h
  apply ht.congr'
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
  have hc : Continuous (fun x : R3 => g (a • x) - g x) :=
    (hg.comp ((continuous_const : Continuous (fun _ : R3 => a)).smul
      (continuous_id : Continuous (fun x : R3 => x)))).sub hg
  have hcomp : HasCompactSupport (fun x : R3 => g (a • x) - g x) :=
    (hgc.comp_smul ha.ne').sub hgc
  have hm : MemLp (fun x : R3 => g (a • x) - g x) 2 (volume : Measure R3) :=
    hc.memLp_of_hasCompactSupport hcomp
  symm
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,one_div] using
    hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)

end OAI.AnisotropicCalderon.DirichletFamily
