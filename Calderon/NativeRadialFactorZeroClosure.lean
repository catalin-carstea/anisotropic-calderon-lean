import Calderon.NativeRadialFactorGradient
import Mathlib.Analysis.SpecificLimits.Basic

/-! Expanded before source in EXPANSION-native-radial-factor-specific-dct-author-v002.json.
Specific radial convergence is proved in the actual native H1 graph norm. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma nativeRadialFactorTruncation_zero :
    nativeRadialFactorTruncation 0 = smoothSobolev nativeRadialFactorSmoothData := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [value_nativeRadialFactorTruncation_ae 0,
    value_smoothSobolev_ae nativeRadialFactorSmoothData,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x htrunc hvalue hx
  have hnorm : ‖x‖ < 1 := by
    change dist x (0 : R3) < 1 at hx
    simpa only [dist_zero_right] using hx
  have hnonneg : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  rw [htrunc,hvalue]
  change max (1-‖x‖^2-0) 0 = 1-‖x‖^2
  rw [sub_zero,max_eq_left hnonneg]

lemma tendsto_value_nativeRadialFactorTruncation :
    Tendsto (fun n : ℕ => TauCeti.W1p.value (nativeRadialFactorTruncation (1/((n:ℝ)+1))))
      atTop (𝓝 (TauCeti.W1p.value (smoothSobolev nativeRadialFactorSmoothData))) := by
  let u := smoothSobolev nativeRadialFactorSmoothData
  let one := smoothSobolev nativeConstantOneSmoothData
  have hshift : Tendsto (fun n : ℕ => u-(1/((n:ℝ)+1)) • one) atTop (𝓝 u) := by
    have h := (continuous_const.sub (continuous_id.smul continuous_const) :
      Continuous (fun t : ℝ => u-t • one)).tendsto 0
    have hs := h.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    change Tendsto (fun n : ℕ => u-(1/((n:ℝ)+1)) • one) atTop (𝓝 (u-(0:ℝ) • one)) at hs
    simpa only [zero_smul,sub_zero] using hs
  have hv := (TauCeti.W1p.valueL.continuous.tendsto u).comp hshift
  have h := (Lp.continuous_posPart.tendsto (TauCeti.W1p.value u)).comp hv
  have he : Lp.posPart (TauCeti.W1p.value u) = TauCeti.W1p.value u := by
    have hz := congrArg TauCeti.W1p.value nativeRadialFactorTruncation_zero
    simpa only [nativeRadialFactorTruncation,zero_smul,sub_zero,
      TauCeti.W1p.value_posPart] using hz
  rw [he] at h
  change Tendsto (fun n : ℕ => Lp.posPart (TauCeti.W1p.value
    (u-(1/((n:ℝ)+1)) • one))) atTop (𝓝 (TauCeti.W1p.value u)) at h
  simpa only [u,one,nativeRadialFactorTruncation,TauCeti.W1p.value_posPart] using h

lemma tendsto_nativeRadialFactorTruncation :
    Tendsto (fun n : ℕ => nativeRadialFactorTruncation (1/((n:ℝ)+1))) atTop
      (𝓝 (smoothSobolev nativeRadialFactorSmoothData)) :=
  TauCeti.W1p.tendsto_iff_value_gradient.mpr
    ⟨tendsto_value_nativeRadialFactorTruncation,tendsto_gradient_nativeRadialFactorTruncation⟩

lemma nativeRadialFactor_mem_zero :
    smoothSobolev nativeRadialFactorSmoothData ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  apply (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed.mem_of_tendsto
    tendsto_nativeRadialFactorTruncation
  apply Eventually.of_forall
  intro n
  apply nativeRadialFactorTruncation_mem_zero
  · positivity
  · apply (div_le_one (by positivity : 0 < (n:ℝ)+1)).mpr
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith

lemma smoothSobolev_radialFactor_mem_zero (q : SmoothData) :
    smoothSobolev
      ⟨fun x : R3 => (1-‖x‖^2)*q.1 x, (contDiff_const.sub (contDiff_norm_sq ℝ)).mul q.2⟩ ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound q
  have hmem : TauCeti.W1p.contDiffSMulL
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      q.1 q.2 hM hm hg (smoothSobolev nativeRadialFactorSmoothData) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule
      (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      q.2 hM hm hg nativeRadialFactor_mem_zero
  have hprod := contDiffSMulL_smoothSobolev q hM hm hg nativeRadialFactorSmoothData
  have hdata : (⟨q.1*nativeRadialFactorSmoothData.1,
      q.2.mul nativeRadialFactorSmoothData.2⟩ : SmoothData) =
      ⟨fun x : R3 => (1-‖x‖^2)*q.1 x, (contDiff_const.sub (contDiff_norm_sq ℝ)).mul q.2⟩ := by
    apply Subtype.ext
    funext x
    exact mul_comm (q.1 x) (1-‖x‖^2)
  have he := hprod.trans (congrArg smoothSobolev hdata)
  exact he ▸ hmem

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeRadialFactorTruncation_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_value_nativeRadialFactorTruncation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_nativeRadialFactorTruncation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeRadialFactor_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSobolev_radialFactor_mem_zero
