import Calderon.NativeSmoothBallRepresentativeGradient
import Calderon.BallScaledDilationContinuity
import Calderon.InwardSmoothBallRealization

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_smoothData_close_of_smooth_ball_representative
    (u : BallH1) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f (ballOpens : Set R3))
    (hValue : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : SmoothData, HasCompactSupport w.1 ∧ ‖smoothSobolev w - u‖ < ε := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  obtain ⟨hfLp,hgLp⟩ := memLp_value_gradient_of_smooth_ball_representative u f hf hValue
  have hGradient : (TauCeti.W1p.gradient u : R3 → R3) =ᵐ[μ] gradient f :=
    gradient_ae_eq_of_smooth_ball_representative u f hf hValue
  let d0 : ℝ → ℝ≥0∞ := fun a =>
    eLpNorm (fun x : R3 => f (a • x) - f x) 2 μ
  let d1 : ℝ → ℝ≥0∞ := fun a =>
    eLpNorm (fun x : R3 => a • gradient f (a • x) - gradient f x) 2 μ
  have h0 : Tendsto d0 (𝓝[<] 1) (𝓝 0) :=
    tendsto_eLpNorm_inward_dilation_sub_of_memLp_ball f hfLp
  have h1 : Tendsto d1 (𝓝[<] 1) (𝓝 0) :=
    tendsto_eLpNorm_scaled_inward_dilation_sub_of_memLp_ball (gradient f) hgLp
  have h0Real : Tendsto (fun a => (d0 a).toReal) (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h0
  have h1Real : Tendsto (fun a => (d1 a).toReal) (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1
  have hSum : Tendsto (fun a => (d0 a).toReal + (d1 a).toReal)
      (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using h0Real.add h1Real
  have hPos : ∀ᶠ a : ℝ in 𝓝[<] 1, 0 < a :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hChoose : ∀ᶠ a : ℝ in 𝓝[<] 1,
      0 < a ∧ a < 1 ∧ (d0 a).toReal + (d1 a).toReal < ε := by
    filter_upwards [hPos,self_mem_nhdsWithin,hSum.eventually (gt_mem_nhds hε)]
      with a ha0 ha1 hSmall
    exact ⟨ha0,ha1,hSmall⟩
  obtain ⟨a,ha0,ha1,hSmall⟩ := hChoose.exists
  obtain ⟨w,hwc,hw⟩ := exists_smoothData_inward_dilation_eq_near_closedBall f hf a ha0 ha1
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have hValueSub : (TauCeti.W1p.value (smoothSobolev w-u) : R3 → ℝ)
      =ᵐ[μ] (fun x : R3 => f (a • x)-f x) := by
    have hmap : TauCeti.W1p.value (smoothSobolev w-u) =
        TauCeti.W1p.value (smoothSobolev w) - TauCeti.W1p.value u :=
      (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_sub _ _
    rw [hmap]
    filter_upwards [Lp.coeFn_sub (TauCeti.W1p.value (smoothSobolev w)) (TauCeti.W1p.value u),
      value_smoothSobolev_ae w,hValue,ae_restrict_mem hB] with x hsub hwx hux hx
    rw [hsub]
    change TauCeti.W1p.value (smoothSobolev w) x - TauCeti.W1p.value u x = _
    rw [hwx,hux,(hw x (ball_subset_closedBall hx)).2.1]
  have hGradientSub : (TauCeti.W1p.gradient (smoothSobolev w-u) : R3 → R3)
      =ᵐ[μ] (fun x : R3 => a • gradient f (a • x)-gradient f x) := by
    have hmap : TauCeti.W1p.gradient (smoothSobolev w-u) =
        TauCeti.W1p.gradient (smoothSobolev w) - TauCeti.W1p.gradient u :=
      (TauCeti.W1p.gradientL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_sub _ _
    rw [hmap]
    filter_upwards [Lp.coeFn_sub (TauCeti.W1p.gradient (smoothSobolev w)) (TauCeti.W1p.gradient u),
      gradient_smoothSobolev_ae w,hGradient,ae_restrict_mem hB] with x hsub hwx hux hx
    rw [hsub]
    change TauCeti.W1p.gradient (smoothSobolev w) x - TauCeti.W1p.gradient u x = _
    rw [hwx,hux,(hw x (ball_subset_closedBall hx)).2.2]
  have hValueNorm : ‖TauCeti.W1p.value (smoothSobolev w-u)‖ = (d0 a).toReal := by
    rw [Lp.norm_def,eLpNorm_congr_ae hValueSub]
  have hGradientNorm : ‖TauCeti.W1p.gradient (smoothSobolev w-u)‖ = (d1 a).toReal := by
    rw [Lp.norm_def,eLpNorm_congr_ae hGradientSub]
  refine ⟨w,hwc,lt_of_le_of_lt ?_ hSmall⟩
  calc
    ‖smoothSobolev w-u‖ ≤ ‖TauCeti.W1p.value (smoothSobolev w-u)‖ +
        ‖TauCeti.W1p.gradient (smoothSobolev w-u)‖ :=
      TauCeti.W1p.norm_le_norm_value_add_norm_gradient (smoothSobolev w-u)
    _ = (d0 a).toReal + (d1 a).toReal := by rw [hValueNorm,hGradientNorm]

end OAI.AnisotropicCalderon.DirichletFamily
