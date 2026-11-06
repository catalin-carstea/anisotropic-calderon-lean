import Calderon.BallMemLpDilationContinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem tendsto_eLpNorm_scaled_inward_dilation_sub_of_memLp_ball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : R3 → V) (hf : MemLp f 2 ((volume : Measure R3).restrict ballOpens)) :
    Tendsto (fun a : ℝ => eLpNorm (fun x : R3 => a • f (a • x) - f x) 2
      ((volume : Measure R3).restrict ballOpens)) (𝓝[<] 1) (𝓝 0) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  have hDiff : Tendsto
      (fun a : ℝ => eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ)
      (𝓝[<] 1) (𝓝 0) :=
    tendsto_eLpNorm_inward_dilation_sub_of_memLp_ball f hf
  have ha : Tendsto (fun a : ℝ => ‖a‖ₑ) (𝓝[<] 1) (𝓝 1) := by
    simpa only [enorm_one] using
      (continuous_enorm.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have haSub : Tendsto (fun a : ℝ => ‖a-1‖ₑ) (𝓝[<] 1) (𝓝 0) := by
    simpa only [id_eq,Function.comp_def,sub_self,enorm_zero] using
      (((show Continuous (fun a : ℝ => a - 1) from
        continuous_id.sub continuous_const).enorm.tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds)
  have hFirst : Tendsto
      (fun a : ℝ => ‖a‖ₑ * eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ)
      (𝓝[<] 1) (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.mul ha (Or.inl one_ne_zero) hDiff (Or.inr ENNReal.one_ne_top)
  have hSecond : Tendsto (fun a : ℝ => ‖a-1‖ₑ * eLpNorm f 2 μ)
      (𝓝[<] 1) (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const haSub (Or.inr hf.eLpNorm_ne_top)
  have hSum : Tendsto (fun a : ℝ =>
      ‖a‖ₑ * eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ +
        ‖a-1‖ₑ * eLpNorm f 2 μ) (𝓝[<] 1) (𝓝 0) := by
    simpa only [zero_add] using hFirst.add hSecond
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum
    (fun _ => bot_le)
  intro a
  have hdecomp : (fun x : R3 => a • f (a • x) - f x) =
      a • (fun x : R3 => f (a • x) - f x) + (a-1) • f := by
    funext x
    change a • f (a • x) - f x = a • (f (a • x) - f x) + (a-1) • f x
    simp only [smul_sub,sub_smul,one_smul]
    abel
  change eLpNorm (fun x : R3 => a • f (a • x) - f x) 2 μ ≤
    ‖a‖ₑ * eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ +
      ‖a-1‖ₑ * eLpNorm f 2 μ
  rw [hdecomp]
  calc
    eLpNorm (a • (fun x : R3 => f (a • x) - f x) + (a-1) • f) 2 μ
      ≤ eLpNorm (a • (fun x : R3 => f (a • x) - f x)) 2 μ +
        eLpNorm ((a-1) • f) 2 μ := eLpNorm_add_le (by norm_num)
    _ = ‖a‖ₑ * eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ +
        ‖a-1‖ₑ * eLpNorm f 2 μ := by rw [eLpNorm_const_smul,eLpNorm_const_smul]

end OAI.AnisotropicCalderon.DirichletFamily
