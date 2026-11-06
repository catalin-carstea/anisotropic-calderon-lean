import Calderon.NativeRadialFactorTruncation
import Calderon.NativeL2DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma gradient_nativeConstantOneSmoothData :
    TauCeti.W1p.gradient (smoothSobolev nativeConstantOneSmoothData) = 0 := by
  apply Lp.ext
  filter_upwards [gradient_smoothSobolev_ae nativeConstantOneSmoothData,
    Lp.coeFn_zero R3 2 ((volume : Measure R3).restrict ballOpens)] with x hx hz
  rw [hx,hz]
  exact gradient_fun_const x (1:ℝ)

lemma gradient_nativeRadialFactorShift (t : ℝ) :
    TauCeti.W1p.gradient
      (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData) =
    TauCeti.W1p.gradient (smoothSobolev nativeRadialFactorSmoothData) := by
  have h : TauCeti.W1p.gradient
      (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData) =
      TauCeti.W1p.gradient (smoothSobolev nativeRadialFactorSmoothData) -
        t • TauCeti.W1p.gradient (smoothSobolev nativeConstantOneSmoothData) := by
    simp only [← TauCeti.W1p.gradientL_apply,map_sub,map_smul]
  rw [h,gradient_nativeConstantOneSmoothData,smul_zero,sub_zero]

lemma gradient_nativeRadialFactorTruncation_ae (t : ℝ) :
    TauCeti.W1p.gradient (nativeRadialFactorTruncation t)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => if 0 < 1-‖x‖^2-t then
        TauCeti.W1p.gradient (smoothSobolev nativeRadialFactorSmoothData) x else 0 := by
  have h := TauCeti.W1p.gradient_posPart_ae (by norm_num : (2:ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
    (smoothSobolev nativeRadialFactorSmoothData-t • smoothSobolev nativeConstantOneSmoothData)
  rw [gradient_nativeRadialFactorShift] at h
  filter_upwards [h,value_nativeRadialFactorShift_ae t] with x hx hv
  simpa only [nativeRadialFactorTruncation,Set.indicator,Set.mem_setOf_eq,hv] using hx

lemma tendsto_gradient_nativeRadialFactorTruncation :
    Tendsto (fun n : ℕ => TauCeti.W1p.gradient (nativeRadialFactorTruncation (1/((n:ℝ)+1))))
      atTop (𝓝 (TauCeti.W1p.gradient (smoothSobolev nativeRadialFactorSmoothData))) := by
  apply tendsto_L2_of_ae_tendsto_of_norm_sub_le
  · intro n
    filter_upwards [gradient_nativeRadialFactorTruncation_ae (1/((n:ℝ)+1))] with x hx
    rw [hx]
    split_ifs <;> simp
  · filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
      gradient_nativeRadialFactorTruncation_ae (1/((n:ℝ)+1))),
      ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx hB
    have hn : ‖x‖ < 1 := by
      change dist x (0:R3) < 1 at hB
      simpa only [dist_zero_right] using hB
    have hr : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x]
    have he : ∀ᶠ n : ℕ in atTop, 1/((n:ℝ)+1) < 1-‖x‖^2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_lt_nhds hr)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    exact (hx n |>.trans (if_pos (sub_pos.mpr hn))).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_nativeConstantOneSmoothData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_nativeRadialFactorShift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.gradient_nativeRadialFactorTruncation_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_gradient_nativeRadialFactorTruncation
