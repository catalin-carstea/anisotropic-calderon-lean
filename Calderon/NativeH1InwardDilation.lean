import Calderon.NativeSmoothH1OrthogonalPullback
import Calderon.NativeSmoothInwardTraceContinuity
import Calderon.LpDilationScaling
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Expanded first in EXPANSION-native-H1-inward-dilation-v001.json.
The uniform bound is derived on the literal smooth realization before the
checked dense extension constructs an operation on the actual native H1 space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Gradient ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem inwardDilation_l2_factor_le_four (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ENNReal.ofReal ((a⁻¹) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) ≤ 4 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hb1 : 1 ≤ a⁻¹ := (one_le_inv₀ ha0).mpr ha1
  have hb2 : a⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ ha0).mpr (by linarith)
  have hp : (a⁻¹) ^ ((3 : ℝ)/2) ≤ (a⁻¹)^2 := by
    calc
      (a⁻¹) ^ ((3 : ℝ)/2) ≤ (a⁻¹) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (show (3 : ℝ)/2 ≤ (2 : ℝ) by norm_num)
      _ = (a⁻¹) ^ (2 : ℕ) := by
        change (a⁻¹) ^ ((2 : ℕ) : ℝ) = (a⁻¹) ^ (2 : ℕ)
        exact Real.rpow_natCast (a⁻¹) 2
  have hsq : (a⁻¹)^2 ≤ (4 : ℝ) := by nlinarith [inv_nonneg.mpr ha0.le]
  have hfactor : (a⁻¹) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal) ≤ 4 := by
    simpa [R3] using hp.trans hsq
  simpa using ENNReal.ofReal_le_ofReal hfactor

theorem eLpNorm_unitBall_inwardDilation_le_four
    {V : Type*} [NormedAddCommGroup V] (f : R3 → V)
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    eLpNorm (fun x : R3 => f (a • x)) 2 ((volume : Measure R3).restrict ballOpens) ≤
      4 * eLpNorm f 2 ((volume : Measure R3).restrict ballOpens) := by
  let F : R3 → V := (ballOpens : Set R3).indicator f
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have he : (fun x : R3 => f (a • x)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => F (a • x)) := by
    filter_upwards [ae_restrict_mem hB] with x hx
    have hxNorm : ‖x‖ < 1 := by
      simpa only [coe_ballOpens, B, mem_ball, dist_zero_right] using hx
    have hax : a • x ∈ (ballOpens : Set R3) := by
      change a • x ∈ ball (0 : R3) 1
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha1 (norm_nonneg x))
        (by simpa only [one_mul] using hxNorm)
    simp only [F, indicator_of_mem hax]
  have hScale : eLpNorm (fun x : R3 => F (a • x)) 2 (volume : Measure R3) =
      ENNReal.ofReal ((a⁻¹) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) *
        eLpNorm F 2 (volume : Measure R3) := by
    simpa only [inv_inv] using eLpNorm_comp_inv_smul_R3 F (inv_pos.mpr ha0) 2
  calc
    eLpNorm (fun x : R3 => f (a • x)) 2 ((volume : Measure R3).restrict ballOpens)
        = eLpNorm (fun x : R3 => F (a • x)) 2 ((volume : Measure R3).restrict ballOpens) :=
          eLpNorm_congr_ae he
    _ ≤ eLpNorm (fun x : R3 => F (a • x)) 2 (volume : Measure R3) :=
      eLpNorm_restrict_le _ _ _ _
    _ = ENNReal.ofReal ((a⁻¹) ^ ((Module.finrank ℝ R3 : ℝ) / (2 : ℝ≥0∞).toReal)) *
        eLpNorm F 2 (volume : Measure R3) := hScale
    _ ≤ 4 * eLpNorm F 2 (volume : Measure R3) :=
      mul_le_mul' (inwardDilation_l2_factor_le_four a ha ha1) le_rfl
    _ = 4 * eLpNorm f 2 ((volume : Measure R3).restrict ballOpens) := by
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hB.nullMeasurableSet]

theorem norm_smoothSobolev_inwardDilation_le_eight
    (f : SmoothData) (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ‖smoothSobolev (smoothData_inwardDilation f a)‖ ≤ 8 * ‖smoothSobolev f‖ := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hv : ‖TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a))‖ ≤
      4 * ‖TauCeti.W1p.value (smoothSobolev f)‖ := by
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (memLp_smooth_value f).eLpNorm_ne_top)
      (eLpNorm_unitBall_inwardDilation_le_four f.1 a ha ha1)
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (value_smoothSobolev_ae (smoothData_inwardDilation f a)),
      eLpNorm_congr_ae (value_smoothSobolev_ae f)]
    simpa [smoothData_inwardDilation, ENNReal.toReal_mul] using ht
  have hGrad : (TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a)) : R3 → R3)
      =ᵐ[μ] (fun x : R3 => a • gradient f.1 (a • x)) := by
    filter_upwards [gradient_smoothSobolev_ae (smoothData_inwardDilation f a)] with x hx
    rw [hx]
    exact gradient_comp_const_smul f.1 a x ((f.2.differentiable (by simp)) (a • x))
  have haNorm : ‖a‖ₑ ≤ (1 : ℝ≥0∞) := by
    have hr : ‖a‖ ≤ (1 : ℝ) := by rw [Real.norm_eq_abs, abs_of_pos ha0]; exact ha1
    calc
      ‖a‖ₑ = ENNReal.ofReal ‖a‖ := (ofReal_norm a).symm
      _ ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hr
      _ = 1 := ENNReal.ofReal_one
  have hGe : eLpNorm (fun x : R3 => a • gradient f.1 (a • x)) 2 μ ≤
      4 * eLpNorm (gradient f.1) 2 μ := by
    calc
      eLpNorm (fun x : R3 => a • gradient f.1 (a • x)) 2 μ =
          ‖a‖ₑ * eLpNorm (fun x : R3 => gradient f.1 (a • x)) 2 μ :=
        eLpNorm_const_smul a (fun x : R3 => gradient f.1 (a • x)) 2 μ
      _ ≤ 1 * (4 * eLpNorm (gradient f.1) 2 μ) :=
        mul_le_mul' haNorm (eLpNorm_unitBall_inwardDilation_le_four (gradient f.1) a ha ha1)
      _ = 4 * eLpNorm (gradient f.1) 2 μ := one_mul _
  have hg : ‖TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a))‖ ≤
      4 * ‖TauCeti.W1p.gradient (smoothSobolev f)‖ := by
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (memLp_smooth_gradient f).eLpNorm_ne_top) hGe
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hGrad,
      eLpNorm_congr_ae (gradient_smoothSobolev_ae f)]
    simpa [ENNReal.toReal_mul] using ht
  calc
    ‖smoothSobolev (smoothData_inwardDilation f a)‖ ≤
        ‖TauCeti.W1p.value (smoothSobolev (smoothData_inwardDilation f a))‖ +
        ‖TauCeti.W1p.gradient (smoothSobolev (smoothData_inwardDilation f a))‖ :=
      TauCeti.W1p.norm_le_norm_value_add_norm_gradient _
    _ ≤ 4 * ‖TauCeti.W1p.value (smoothSobolev f)‖ +
        4 * ‖TauCeti.W1p.gradient (smoothSobolev f)‖ := add_le_add hv hg
    _ ≤ 4 * ‖smoothSobolev f‖ + 4 * ‖smoothSobolev f‖ := add_le_add
      (mul_le_mul_of_nonneg_left (TauCeti.W1p.norm_value_le _) (by norm_num))
      (mul_le_mul_of_nonneg_left (TauCeti.W1p.norm_gradient_le _) (by norm_num))
    _ = 8 * ‖smoothSobolev f‖ := by ring

def nativeSmoothInwardDilationLinear (a : ℝ) :
    nativeSmoothFunctionSpace →ₗ[ℝ] nativeSmoothFunctionSpace where
  toFun f := ⟨fun x : R3 => f.1 (a • x),
    (show ContDiff ℝ ∞ f.1 from f.2).comp ((a • ContinuousLinearMap.id ℝ R3).contDiff)⟩
  map_add' f g := rfl
  map_smul' c f := rfl

def nativeH1InwardDilation (a : ℝ) : BallH1 →L[ℝ] BallH1 :=
  (nativeSmoothSobolevLinear.comp (nativeSmoothInwardDilationLinear a)).extendOfNorm
    nativeSmoothSobolevLinear

theorem nativeH1InwardDilation_smoothLinear
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (f : nativeSmoothFunctionSpace) :
    nativeH1InwardDilation a (nativeSmoothSobolevLinear f) =
      nativeSmoothSobolevLinear (nativeSmoothInwardDilationLinear a f) :=
  LinearMap.extendOfNorm_eq denseRange_nativeSmoothSobolevLinear
    ⟨8, fun q => norm_smoothSobolev_inwardDilation_le_eight ⟨q.1, q.2⟩ a ha ha1⟩ f

theorem nativeH1InwardDilation_smoothSobolev
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (f : SmoothData) :
    nativeH1InwardDilation a (smoothSobolev f) =
      smoothSobolev (smoothData_inwardDilation f a) :=
  nativeH1InwardDilation_smoothLinear a ha ha1 ⟨f.1, f.2⟩

theorem norm_nativeH1InwardDilation_le_eight
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ‖nativeH1InwardDilation a‖ ≤ 8 :=
  LinearMap.opNorm_extendOfNorm_le denseRange_nativeSmoothSobolevLinear (by norm_num)
    (fun q => norm_smoothSobolev_inwardDilation_le_eight ⟨q.1, q.2⟩ a ha ha1)

theorem norm_nativeH1InwardDilation_apply_le_eight
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (u : BallH1) :
    ‖nativeH1InwardDilation a u‖ ≤ 8 * ‖u‖ :=
  ((nativeH1InwardDilation a).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_nativeH1InwardDilation_le_eight a ha ha1) (norm_nonneg u))

attribute [local irreducible] nativeH1InwardDilation

theorem tendsto_nativeH1InwardDilation_apply_one (u : BallH1) :
    Tendsto (fun a : ℝ => nativeH1InwardDilation a u) (𝓝[<] 1) (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨f, _, hf⟩ := exists_compactSupport_smoothData_native_H1_approximation
    u (ε/20) (by positivity)
  let w : BallH1 := smoothSobolev f
  have hAge : ∀ᶠ a : ℝ in 𝓝[<] 1, (1/2 : ℝ) ≤ a :=
    Filter.Eventually.mono
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))) (fun _ h => h.le)
  have hAle : ∀ᶠ a : ℝ in 𝓝[<] 1, a ≤ 1 :=
    by
      have hMem : ∀ᶠ a : ℝ in 𝓝[<] 1, a < 1 := self_mem_nhdsWithin
      exact Filter.Eventually.mono hMem (fun _ h => h.le)
  have he : (fun a : ℝ => nativeH1InwardDilation a w) =ᶠ[𝓝[<] 1]
      (fun a : ℝ => smoothSobolev (smoothData_inwardDilation f a)) := by
    filter_upwards [hAge, hAle] with a ha ha1
    exact nativeH1InwardDilation_smoothSobolev a ha ha1 f
  have hw : Tendsto (fun a : ℝ => nativeH1InwardDilation a w) (𝓝[<] 1) (𝓝 w) :=
    (Filter.tendsto_congr' he).mpr (tendsto_smoothSobolev_inwardDilation f)
  have hwSmall : ∀ᶠ a : ℝ in 𝓝[<] 1, ‖nativeH1InwardDilation a w-w‖ < ε/2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hw).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hAge, hAle, hwSmall] with a ha ha1 haw
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hid : nativeH1InwardDilation a u-u =
      nativeH1InwardDilation a (u-w)+(nativeH1InwardDilation a w-w)+(w-u) := by
    rw [map_sub]
    abel
  have hwu : ‖w-u‖ < ε/20 := hf
  have huw : ‖u-w‖ < ε/20 := by simpa only [norm_sub_rev] using hwu
  calc
    ‖nativeH1InwardDilation a u-u‖ =
        ‖nativeH1InwardDilation a (u-w)+(nativeH1InwardDilation a w-w)+(w-u)‖ :=
      congrArg norm hid
    _ ≤ ‖nativeH1InwardDilation a (u-w)‖ + ‖nativeH1InwardDilation a w-w‖ + ‖w-u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 8 * ‖u-w‖ + ‖nativeH1InwardDilation a w-w‖ + ‖w-u‖ :=
      add_le_add (add_le_add (norm_nativeH1InwardDilation_apply_le_eight a ha ha1 (u-w)) le_rfl) le_rfl
    _ < 8*(ε/20)+ε/2+ε/20 :=
      add_lt_add (add_lt_add (mul_lt_mul_of_pos_left huw (by norm_num)) haw) hwu
    _ < ε := by linarith

theorem tendsto_nativeH1InwardDilation_variable_one
    (U : ℝ → BallH1) (u : BallH1) (hU : Tendsto U (𝓝[<] 1) (𝓝 u)) :
    Tendsto (fun a : ℝ => nativeH1InwardDilation a (U a)) (𝓝[<] 1) (𝓝 u) := by
  have hDiff : Tendsto (fun a => ‖U a-u‖) (𝓝[<] 1) (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hU
  have hFix : Tendsto (fun a => ‖nativeH1InwardDilation a u-u‖) (𝓝[<] 1) (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_nativeH1InwardDilation_apply_one u)
  have hControl : Tendsto (fun a => 8*‖U a-u‖ + ‖nativeH1InwardDilation a u-u‖)
      (𝓝[<] 1) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_add] using (hDiff.const_mul 8).add hFix
  have hBound : ∀ᶠ a : ℝ in 𝓝[<] 1,
      ‖nativeH1InwardDilation a (U a)-u‖ ≤ 8*‖U a-u‖ + ‖nativeH1InwardDilation a u-u‖ := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (1/2 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with a ha ha1
    have hid : nativeH1InwardDilation a (U a)-u =
        nativeH1InwardDilation a (U a-u)+(nativeH1InwardDilation a u-u) := by
      rw [map_sub]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_nativeH1InwardDilation_apply_le_eight a ha.le ha1.le (U a-u)) le_rfl)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hBound hControl)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inwardDilation_l2_factor_le_four
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eLpNorm_unitBall_inwardDilation_le_four
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_smoothSobolev_inwardDilation_le_eight
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothInwardDilationLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1InwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1InwardDilation_smoothLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1InwardDilation_smoothSobolev
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeH1InwardDilation_le_eight
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeH1InwardDilation_apply_le_eight
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_nativeH1InwardDilation_apply_one
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_nativeH1InwardDilation_variable_one
