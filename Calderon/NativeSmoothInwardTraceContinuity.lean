import Calderon.BallScaledDilationContinuity
import Calderon.InwardSmoothBallRealization
import Calderon.NativeFullSharpHalfTrace

/-! This proves a genuine native restriction/trace limit for each fixed smooth
representative. No metric harmonic density or native-to-smooth theorem is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace

def smoothData_inwardDilation (f : SmoothData) (a : ℝ) : SmoothData :=
  ⟨fun x : R3 => f.1 (a • x), f.2.comp ((a • ContinuousLinearMap.id ℝ R3).contDiff)⟩

theorem tendsto_smoothSobolev_inwardDilation (f : SmoothData) :
    Tendsto (fun a : ℝ => smoothSobolev (smoothData_inwardDilation f a))
      (𝓝[<] 1) (𝓝 (smoothSobolev f)) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let d0 : ℝ → ℝ≥0∞ := fun a => eLpNorm (fun x : R3 => f.1 (a • x) - f.1 x) 2 μ
  let d1 : ℝ → ℝ≥0∞ := fun a =>
    eLpNorm (fun x : R3 => a • gradient f.1 (a • x) - gradient f.1 x) 2 μ
  have h0 : Tendsto d0 (𝓝[<] 1) (𝓝 0) :=
    tendsto_eLpNorm_inward_dilation_sub_of_memLp_ball f.1 (memLp_smooth_value f)
  have h1 : Tendsto d1 (𝓝[<] 1) (𝓝 0) :=
    tendsto_eLpNorm_scaled_inward_dilation_sub_of_memLp_ball
      (gradient f.1) (memLp_smooth_gradient f)
  have h0Real : Tendsto (fun a => (d0 a).toReal) (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h0
  have h1Real : Tendsto (fun a => (d1 a).toReal) (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1
  have hSum : Tendsto (fun a => (d0 a).toReal + (d1 a).toReal)
      (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using h0Real.add h1Real
  have hValue (a : ℝ) :
      (TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f) : R3 → ℝ)
        =ᵐ[μ] (fun x => f.1 (a • x) - f.1 x) := by
    have hmap : TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f) =
        TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a)) -
          TauCeti.W1p.value (smoothSobolev f) :=
      (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_sub _ _
    rw [hmap]
    filter_upwards [Lp.coeFn_sub (TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a)))
      (TauCeti.W1p.value (smoothSobolev f)), value_smoothSobolev_ae (smoothData_inwardDilation f a),
      value_smoothSobolev_ae f] with x hsub hD hF
    rw [hsub]
    change TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a)) x -
      TauCeti.W1p.value (smoothSobolev f) x = _
    rw [hD, hF]
    rfl
  have hGradient (a : ℝ) :
      (TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f) : R3 → R3)
        =ᵐ[μ] (fun x => a • gradient f.1 (a • x) - gradient f.1 x) := by
    have hmap : TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f) =
        TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a)) -
          TauCeti.W1p.gradient (smoothSobolev f) :=
      (TauCeti.W1p.gradientL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_sub _ _
    rw [hmap]
    filter_upwards [Lp.coeFn_sub (TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a)))
      (TauCeti.W1p.gradient (smoothSobolev f)), gradient_smoothSobolev_ae (smoothData_inwardDilation f a),
      gradient_smoothSobolev_ae f] with x hsub hD hF
    rw [hsub]
    change TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a)) x -
      TauCeti.W1p.gradient (smoothSobolev f) x = _
    rw [hD, hF]
    change gradient (fun y : R3 => f.1 (a • y)) x - gradient f.1 x = _
    rw [gradient_comp_const_smul f.1 a x ((f.2.differentiable (by simp)) (a • x))]
  have hBound (a : ℝ) :
      ‖smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f‖ ≤
        (d0 a).toReal + (d1 a).toReal := by
    have hV : ‖TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f)‖ =
        (d0 a).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hValue a)]
    have hG : ‖TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f)‖ =
        (d1 a).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (hGradient a)]
    exact (TauCeti.W1p.norm_le_norm_value_add_norm_gradient
      (smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f)).trans
        (le_of_eq (congrArg₂ (fun x y : ℝ => x+y) hV hG))
  have hNorm : Tendsto (fun a : ℝ =>
      ‖smoothSobolev (smoothData_inwardDilation f a) - smoothSobolev f‖)
      (𝓝[<] 1) (𝓝 (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum
      (fun _ => norm_nonneg _) hBound
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm

theorem tendsto_nativeHalfTrace_smoothData_inwardDilation
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SmoothData) :
    Tendsto (fun a : ℝ => nativeHalfTraceL hF hO hD τ0
      (smoothSobolev (smoothData_inwardDilation f a))) (𝓝[<] 1)
      (𝓝 (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))) :=
  ((nativeHalfTraceL hF hO hD τ0).continuous.tendsto (smoothSobolev f)).comp
    (tendsto_smoothSobolev_inwardDilation f)

theorem tendsto_radius_ratio_from_above (r : ℝ) (hr : 0 < r) :
    Tendsto (fun η : ℝ => r/(r+η)) (𝓝[>] 0) (𝓝[<] 1) := by
  have hAdd : Tendsto (fun η : ℝ => r+η) (𝓝[>] 0) (𝓝 r) := by
    simpa only [add_zero, Pi.add_apply, Function.comp_def, id_eq] using
      (show Tendsto (fun _ : ℝ => r) (𝓝[>] 0) (𝓝 r) from tendsto_const_nhds).add
        (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hRatio : Tendsto (fun η : ℝ => r/(r+η)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hRaw : Tendsto ((fun _ : ℝ => r) / (fun η : ℝ => r+η))
        (𝓝[>] 0) (𝓝 (r/r)) :=
      (show Tendsto (fun _ : ℝ => r) (𝓝[>] 0) (𝓝 r) from tendsto_const_nhds).div hAdd hr.ne'
    have hExpr : ((fun _ : ℝ => r) / (fun η : ℝ => r+η)) =
        (fun η : ℝ => r/(r+η)) := by
      funext η
      rfl
    rw [hExpr] at hRaw
    simpa only [div_self hr.ne'] using hRaw
  have hBelow : ∀ᶠ η : ℝ in 𝓝[>] 0, r/(r+η) < 1 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    exact (div_lt_one (by linarith : 0 < r+η)).mpr (by linarith)
  exact tendsto_nhdsWithin_iff.mpr ⟨hRatio, hBelow⟩

theorem tendsto_nativeHalfTrace_enlarged_radius_restriction
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SmoothData) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun η : ℝ => nativeHalfTraceL hF hO hD τ0
      (smoothSobolev (smoothData_inwardDilation f (r/(r+η))))) (𝓝[>] 0)
      (𝓝 (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))) :=
  (tendsto_nativeHalfTrace_smoothData_inwardDilation hF hO hD τ0 f).comp
    (tendsto_radius_ratio_from_above r hr)

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.smoothData_inwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.tendsto_smoothSobolev_inwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.tendsto_nativeHalfTrace_smoothData_inwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.tendsto_radius_ratio_from_above
#print axioms OAI.AnisotropicCalderon.DirichletFamily.tendsto_nativeHalfTrace_enlarged_radius_restriction
