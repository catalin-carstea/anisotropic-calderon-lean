import Calderon.UnitBallValueTraceKernel
import Calderon.NativeSmoothBoundaryZeroClosure
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Helpers for task 11 (`UnitBallValueTraceKernel`): a boundary-layer Hardy estimate in polar
coordinates, a radial cutoff, and the resulting distance bound to `H¹₀`. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.TraceKernel
open SphereHarmonic EnergyBridge DirichletFamily


theorem radial_sq_bound {g g' : ℝ → ℝ} (hg : ∀ r, HasDerivAt g (g' r) r) (hg' : Continuous g')
    {a : ℝ} (ha : a ≤ 1) :
    ∫ r in a..1, g r ^ 2 ≤ 2 * (1 - a) * g 1 ^ 2 + 4 * (1 - a) ^ 2 * ∫ r in a..1, g' r ^ 2 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun r => (hg r).continuousAt
  have hF : ∀ r ∈ uIcc a 1, HasDerivAt (fun r => (r - a) * g r ^ 2)
      (g r ^ 2 + 2 * (r - a) * g r * g' r) r := by
    intro r _
    have h1 : HasDerivAt (fun r => r - a) 1 r := (hasDerivAt_id r).sub_const a
    have h2 := (hg r).pow 2
    convert h1.mul h2 using 1
    simp; ring
  have hFint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun r => g r ^ 2 + 2 * (r - a) * g r * g' r).intervalIntegrable _ _)
  simp only [sub_self, zero_mul, sub_zero] at hFint
  have hmono : ∫ r in a..1, ((1/2) * g r ^ 2 - 2 * (1 - a) ^ 2 * g' r ^ 2) ≤
      ∫ r in a..1, (g r ^ 2 + 2 * (r - a) * g r * g' r) := by
    refine intervalIntegral.integral_mono_on ha
      ((by fun_prop : Continuous fun r => (1/2) * g r ^ 2 - 2 * (1 - a) ^ 2 * g' r ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r => g r ^ 2 + 2 * (r - a) * g r * g' r).intervalIntegrable _ _)
      ?_
    intro r hr
    have h0 : 0 ≤ r - a := by linarith [hr.1]
    have h1 : r - a ≤ 1 - a := by linarith [hr.2]
    have h3 : (r - a) ^ 2 ≤ (1 - a) ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg (g r + 2 * (r - a) * g' r), sq_nonneg (g' r)]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  · linarith
  · exact ((by fun_prop : Continuous fun r => (1/2) * g r ^ 2).intervalIntegrable _ _)
  · exact ((by fun_prop : Continuous fun r => 2 * (1 - a) ^ 2 * g' r ^ 2).intervalIntegrable _ _)
theorem norm_gradient_eq_norm_fderiv (f : R3 → ℝ) (x : R3) : ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
  simp only [gradient, LinearIsometryEquiv.norm_map]


theorem radial_layer_real (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (w : R3) (hw : ‖w‖ = 1) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∫ r in Ioo (1 - ε) 1, r ^ 2 * f (r • w) ^ 2 ≤
      2 * ε * f w ^ 2 + 16 * ε ^ 2 * ∫ r in Ioo (1 - ε) 1, r ^ 2 * ‖∇ f (r • w)‖ ^ 2 := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (r • w)) (fderiv ℝ f (r • w) w) r := by
    intro r
    have := ((hf.differentiable (by simp)) (r • w)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const w)
    rw [one_smul] at this
    exact this
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous fun r : ℝ => fderiv ℝ f (r • w) w := by
    have := hf.continuous_fderiv (by simp)
    fun_prop
  have hgc : Continuous fun r : ℝ => ‖∇ f (r • w)‖ := by
    have := hf.continuous_fderiv (n := ∞) (by simp)
    simp only [norm_gradient_eq_norm_fderiv]
    fun_prop
  have ha : 1 - ε ≤ 1 := by linarith
  have hIoo : ∀ {F : ℝ → ℝ}, ∫ r in Ioo (1 - ε) 1, F r = ∫ r in (1 - ε)..1, F r := by
    intro F
    rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
  have hrad := radial_sq_bound hd hdc ha
  simp only [one_smul, sub_sub_cancel] at hrad
  have h1 : ∫ r in Ioo (1 - ε) 1, r ^ 2 * f (r • w) ^ 2 ≤ ∫ r in Ioo (1 - ε) 1, f (r • w) ^ 2 := by
    rw [hIoo, hIoo]
    refine intervalIntegral.integral_mono_on ha
      ((by fun_prop : Continuous fun r : ℝ => r ^ 2 * f (r • w) ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r : ℝ => f (r • w) ^ 2).intervalIntegrable _ _) ?_
    intro r hr
    have h0 : 0 ≤ r := by linarith [hr.1]
    have : r ^ 2 ≤ 1 := by nlinarith [hr.2]
    nlinarith [sq_nonneg (f (r • w))]
  have h2 : ∫ r in (1 - ε)..1, fderiv ℝ f (r • w) w ^ 2 ≤
      4 * ∫ r in (1 - ε)..1, r ^ 2 * ‖∇ f (r • w)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ha
      ((by fun_prop : Continuous fun r : ℝ => fderiv ℝ f (r • w) w ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r : ℝ => 4 * (r ^ 2 * ‖∇ f (r • w)‖ ^ 2)).intervalIntegrable _ _) ?_
    intro r hr
    have hr2 : 1 / 4 ≤ r ^ 2 := by nlinarith [hr.1]
    have hle : |fderiv ℝ f (r • w) w| ≤ ‖∇ f (r • w)‖ := by
      rw [norm_gradient_eq_norm_fderiv, ← Real.norm_eq_abs]
      simpa [hw] using (fderiv ℝ f (r • w)).le_opNorm w
    have hsq : fderiv ℝ f (r • w) w ^ 2 ≤ ‖∇ f (r • w)‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    nlinarith [sq_nonneg ‖∇ f (r • w)‖]
  have e1 := hIoo (F := fun r => f (r • w) ^ 2)
  have e2 := hIoo (F := fun r => r ^ 2 * ‖∇ f (r • w)‖ ^ 2)
  beta_reduce at e1 e2
  rw [e2]
  nlinarith [sq_nonneg ε]

theorem lintegral_polar (F : R3 → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ w : UnitSphere, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ 2) * F (r • (w : R3)))
      ∂surfaceMeasure := by
  have hdim : Module.finrank ℝ R3 - 1 = 2 := by simp
  have mp := (volume : Measure R3).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at mp
  calc ∫⁻ x, F x
      = ∫⁻ x : ({(0:R3)}ᶜ : Set R3), F x.1 ∂((volume : Measure R3).comap (↑)) := by
        rw [lintegral_subtype_comap (measurableSet_singleton _).compl F,
          restrict_compl_singleton]
    _ = ∫⁻ p : UnitSphere × Set.Ioi (0:ℝ), F ((homeomorphUnitSphereProd R3).symm p).1
          ∂(surfaceMeasure.prod (Measure.volumeIoiPow 2)) := by
        have := mp.lintegral_comp_emb (Homeomorph.measurableEmbedding _)
          (fun p ↦ F ((homeomorphUnitSphereProd R3).symm p).1)
        simp only [Homeomorph.symm_apply_apply] at this
        exact this
    _ = ∫⁻ w : UnitSphere, (∫⁻ r : Set.Ioi (0:ℝ), F (r.1 • (w : R3)) ∂(Measure.volumeIoiPow 2))
          ∂surfaceMeasure := by
        rw [lintegral_prod]
        · rfl
        · exact (hF.comp (continuous_subtype_val.comp
            (homeomorphUnitSphereProd R3).symm.continuous).measurable).aemeasurable
    _ = _ := by
        congr 1; ext w
        unfold Measure.volumeIoiPow
        rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
          (g := fun r : Ioi (0:ℝ) => F (r.1 • (w : R3))) (hF.comp (by fun_prop))]
        exact lintegral_subtype_comap measurableSet_Ioi
          (fun r => ENNReal.ofReal (r ^ 2) * F (r • (w : R3)))


/-- The open boundary layer `{1 - ε < ‖x‖ < 1}`. -/
def layer (ε : ℝ) : Set R3 := {x | 1 - ε < ‖x‖ ∧ ‖x‖ < 1}

theorem measurableSet_layer (ε : ℝ) : MeasurableSet (layer ε) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem smul_mem_layer_iff {ε : ℝ} (w : UnitSphere) {r : ℝ} (hr : 0 < r) :
    r • (w : R3) ∈ layer ε ↔ r ∈ Ioo (1 - ε) 1 := by
  simp [layer, norm_smul, abs_of_pos hr]

theorem lintegral_radial_indicator (G : R3 → ENNReal) {ε : ℝ} (hε : ε < 1) (w : UnitSphere) :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ 2) * (layer ε).indicator G (r • (w : R3)) =
      ∫⁻ r in Ioo (1 - ε) 1, ENNReal.ofReal (r ^ 2) * G (r • (w : R3)) := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioi]
  congr 1; ext r
  by_cases hr : 0 < r
  · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
    by_cases h : r ∈ Ioo (1 - ε) 1
    · rw [indicator_of_mem ((smul_mem_layer_iff w hr).2 h), indicator_of_mem h]
    · rw [indicator_of_notMem (fun h' => h ((smul_mem_layer_iff w hr).1 h')),
        indicator_of_notMem h, mul_zero]
  · rw [indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr), indicator_of_notMem]
    intro h; exact hr (by linarith [h.1])


theorem lintegral_layer_eq (G : R3 → ℝ) (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) {ε : ℝ} (hε : ε < 1) :
    ∫⁻ x in layer ε, ENNReal.ofReal (G x) = ∫⁻ w : UnitSphere,
      ENNReal.ofReal (∫ r in Ioo (1 - ε) 1, r ^ 2 * G (r • (w : R3))) ∂surfaceMeasure := by
  rw [← lintegral_indicator (measurableSet_layer ε),
    lintegral_polar _ ((hG.measurable.ennreal_ofReal).indicator (measurableSet_layer ε))]
  congr 1; ext w
  rw [lintegral_radial_indicator _ hε w]
  have hc : Continuous fun r : ℝ => r ^ 2 * G (r • (w : R3)) := by fun_prop
  rw [ofReal_integral_eq_lintegral_ofReal
    ((hc.integrableOn_Icc (a := 1 - ε) (b := 1)).mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall fun r => mul_nonneg (sq_nonneg r) (hG0 _))]
  refine lintegral_congr fun r => ?_
  rw [ENNReal.ofReal_mul (sq_nonneg r)]

theorem hardy_layer_lintegral (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 2) :
    ∫⁻ x in layer ε, ENNReal.ofReal (f x ^ 2) ≤
      ENNReal.ofReal (2 * ε) * ∫⁻ w : UnitSphere, ENNReal.ofReal (f w ^ 2) ∂surfaceMeasure +
      ENNReal.ofReal (16 * ε ^ 2) * ∫⁻ x in layer ε, ENNReal.ofReal (‖∇ f x‖ ^ 2) := by
  have hε1 : ε < 1 := by linarith
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous fun x => ‖∇ f x‖ := by
    have := hf.continuous_fderiv (n := ∞) (by simp)
    simp only [norm_gradient_eq_norm_fderiv]
    fun_prop
  rw [lintegral_layer_eq (fun x => f x ^ 2) (by fun_prop) (fun x => sq_nonneg _) hε1,
    lintegral_layer_eq (fun x => ‖∇ f x‖ ^ 2) (by fun_prop) (fun x => sq_nonneg _) hε1,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left ((by fun_prop : Continuous fun w : UnitSphere => f w ^ 2).measurable.ennreal_ofReal.const_mul _)]
  refine lintegral_mono fun w => ?_
  have hw : ‖(w : R3)‖ = 1 := norm_eq_of_mem_sphere w
  have hI : 0 ≤ ∫ r in Ioo (1 - ε) 1, r ^ 2 * ‖∇ f (r • (w : R3))‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun r _ => by positivity
  calc ENNReal.ofReal (∫ r in Ioo (1 - ε) 1, r ^ 2 * f (r • (w : R3)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε * f w ^ 2 +
          16 * ε ^ 2 * ∫ r in Ioo (1 - ε) 1, r ^ 2 * ‖∇ f (r • (w : R3))‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (radial_layer_real f hf w hw hε0 hε)
    _ = ENNReal.ofReal (2 * ε) * ENNReal.ofReal (f w ^ 2) + ENNReal.ofReal (16 * ε ^ 2) *
          ENNReal.ofReal (∫ r in Ioo (1 - ε) 1, r ^ 2 * ‖∇ f (r • (w : R3))‖ ^ 2) := by
        have h1 : 0 ≤ 2 * ε * f w ^ 2 := by positivity
        have h2 : 0 ≤ 16 * ε ^ 2 * ∫ r in Ioo (1 - ε) 1, r ^ 2 * ‖∇ f (r • (w : R3))‖ ^ 2 :=
          mul_nonneg (by positivity) hI
        rw [ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul (p := 2 * ε) (by positivity),
          ENNReal.ofReal_mul (p := 16 * ε ^ 2) (by positivity)]

/-! ### The radial cutoff -/

/-- A smooth radial cutoff: `0` on `‖x‖ < 1 - ε/2`, `1` on the unit sphere. -/
def cutoff (ε : ℝ) (x : R3) : ℝ := Real.smoothTransition ((‖x‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε))

theorem contDiff_cutoff (ε : ℝ) : ContDiff ℝ ∞ (cutoff ε) := by
  unfold cutoff
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp
    (((contDiff_norm_sq ℝ).sub contDiff_const).mul contDiff_const)

theorem cutoff_eq_zero {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) {x : R3} (hx : ‖x‖ < 1 - ε / 2) :
    cutoff ε x = 0 := by
  unfold cutoff
  apply Real.smoothTransition.zero_of_nonpos
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have : ‖x‖ ^ 2 < (1 - ε / 2) ^ 2 := by nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem cutoff_eq_one {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) {x : R3} (hx : ‖x‖ = 1) :
    cutoff ε x = 1 := by
  unfold cutoff
  apply Real.smoothTransition.one_of_one_le
  rw [hx]
  have : (1 ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε) = 2 - ε / 2 := by field_simp; ring
  rw [this]; linarith

theorem abs_cutoff_le (ε : ℝ) (x : R3) : |cutoff ε x| ≤ 1 := by
  unfold cutoff
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem exists_deriv_smoothTransition_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv Real.smoothTransition t| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hsupp : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 1)) fun t ht => ?_
    by_cases h : t < 0
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 :=
        Filter.mem_of_superset (Iio_mem_nhds h) fun s hs => Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
      rw [this.deriv_eq]; simp
    by_cases h' : 1 < t
    · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 :=
        Filter.mem_of_superset (Ioi_mem_nhds h') fun s hs => Real.smoothTransition.one_of_one_le (le_of_lt hs)
      rw [this.deriv_eq]; simp
    exact absurd ⟨not_lt.1 h, not_lt.1 h'⟩ ht
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hsupp
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

theorem norm_fderiv_cutoff_le {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M)
    {ε : ℝ} (hε0 : 0 < ε) {x : R3} (hx : ‖x‖ ≤ 1) :
    ‖fderiv ℝ (cutoff ε) x‖ ≤ 4 * M / ε := by
  have hφ : HasFDerivAt (fun y : R3 => (‖y‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε))
      ((2 / ε) • (2 • innerSL ℝ x)) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const _).mul_const _
  have hh : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((‖x‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε)))
      ((‖x‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have hc := hh.comp_hasFDerivAt x hφ
  rw [show cutoff ε = Real.smoothTransition ∘
    (fun y : R3 => (‖y‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε)) from rfl, hc.fderiv]
  have e : (2 : ℕ) • innerSL ℝ x = (2 : ℝ) • innerSL ℝ x := by rw [two_smul, two_smul]
  rw [e, norm_smul, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 / ε), abs_two]
  have h1 := hM ((‖x‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε))
  have h3 : 0 ≤ ‖x‖ := norm_nonneg x
  calc |deriv Real.smoothTransition ((‖x‖ ^ 2 - (1 - ε / 2) ^ 2) * (2 / ε))| * (2 / ε * (2 * ‖x‖))
      ≤ M * (2 / ε * (2 * 1)) := by gcongr
    _ = 4 * M / ε := by ring

theorem not_mem_layer_lt {ε : ℝ} {x : R3} (hx : ‖x‖ < 1) (_hε0 : 0 < ε) (h : x ∉ layer ε) :
    ‖x‖ < 1 - ε / 2 := by
  simp only [layer, mem_ofPred_eq, not_and, not_lt] at h
  by_contra h'
  have := h (by linarith)
  linarith

theorem cutoffMul_sq_le {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (f : R3 → ℝ) {x : R3} (hx : ‖x‖ < 1) :
    (cutoff ε x * f x) ^ 2 ≤ (layer ε).indicator (fun y => f y ^ 2) x := by
  by_cases h : x ∈ layer ε
  · rw [indicator_of_mem h, mul_pow]
    have h1 := abs_cutoff_le ε x
    have h2 : cutoff ε x ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (cutoff ε x)]
    nlinarith [sq_nonneg (f x)]
  · rw [indicator_of_notMem h, cutoff_eq_zero hε0 hε (not_mem_layer_lt hx hε0 h)]
    simp

theorem gradient_cutoffMul_sq_le {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) {x : R3} (hx : ‖x‖ < 1) :
    ‖∇ (fun y => cutoff ε y * f y) x‖ ^ 2 ≤
      (layer ε).indicator (fun y => 2 * ‖∇ f y‖ ^ 2 + 32 * M ^ 2 / ε ^ 2 * f y ^ 2) x := by
  by_cases h : x ∈ layer ε
  · rw [indicator_of_mem h, norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv]
    have hζ : DifferentiableAt ℝ (cutoff ε) x :=
      ((contDiff_cutoff ε).differentiable (by simp)) x
    have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
    rw [fderiv_fun_mul hζ hfd]
    have hD := norm_fderiv_cutoff_le hM0 hM hε0 hx.le
    have h1 := abs_cutoff_le ε x
    have hle : ‖cutoff ε x • fderiv ℝ f x + f x • fderiv ℝ (cutoff ε) x‖ ≤
        ‖fderiv ℝ f x‖ + |f x| * (4 * M / ε) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      gcongr
      · calc |cutoff ε x| * ‖fderiv ℝ f x‖ ≤ 1 * ‖fderiv ℝ f x‖ := by gcongr
          _ = _ := one_mul _
    have hpos : 0 ≤ ‖cutoff ε x • fderiv ℝ f x + f x • fderiv ℝ (cutoff ε) x‖ := norm_nonneg _
    have hsq : (|f x| * (4 * M / ε)) ^ 2 = 16 * M ^ 2 / ε ^ 2 * f x ^ 2 := by
      rw [mul_pow, sq_abs]; field_simp; ring
    have hb : 0 ≤ |f x| * (4 * M / ε) := by positivity
    have hN := pow_le_pow_left₀ hpos hle 2
    have key : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
      nlinarith [sq_nonneg (a - b)]
    have := key ‖fderiv ℝ f x‖ (|f x| * (4 * M / ε))
    rw [hsq, show 2 * (16 * M ^ 2 / ε ^ 2 * f x ^ 2) = 32 * M ^ 2 / ε ^ 2 * f x ^ 2 by ring]
      at this
    linarith
  · rw [indicator_of_notMem h]
    have hev : (fun y => cutoff ε y * f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : R3 | ‖y‖ < 1 - ε / 2} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds (not_mem_layer_lt hx hε0 h)] with y hy
      rw [cutoff_eq_zero hε0 hε hy, zero_mul]
    rw [hev.gradient_eq]
    simp

/-! ### Real form of the Hardy estimate -/

theorem layer_subset_closedBall (ε : ℝ) : layer ε ⊆ Metric.closedBall (0 : R3) 1 := fun x hx => by
  simp only [Metric.mem_closedBall, dist_zero_right]; exact hx.2.le

theorem layer_subset_B (ε : ℝ) : layer ε ⊆ B := fun x hx => by
  simp only [B, Metric.mem_ball, dist_zero_right]; exact hx.2

theorem integrableOn_of_continuous {F : R3 → ℝ} (hF : Continuous F) {S : Set R3}
    (hS : S ⊆ Metric.closedBall (0 : R3) 1) : IntegrableOn F S :=
  (hF.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set hS

theorem integrable_sphere_of_continuous {F : R3 → ℝ} (hF : Continuous F) :
    Integrable (fun w : UnitSphere => F w) surfaceMeasure := by
  have hc : Continuous fun w : UnitSphere => F w := hF.comp continuous_subtype_val
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem hardy_layer (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∫ x in layer ε, f x ^ 2 ≤
      2 * ε * ∫ w : UnitSphere, f w ^ 2 ∂surfaceMeasure +
      16 * ε ^ 2 * ∫ x in layer ε, ‖∇ f x‖ ^ 2 := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous fun x => ‖∇ f x‖ := by
    have := hf.continuous_fderiv (n := ∞) (by simp)
    simp only [norm_gradient_eq_norm_fderiv]
    fun_prop
  have h := hardy_layer_lintegral f hf hε0 hε
  have hS0 : 0 ≤ ∫ w : UnitSphere, f w ^ 2 ∂surfaceMeasure := integral_nonneg fun _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ x in layer ε, ‖∇ f x‖ ^ 2 := setIntegral_nonneg (measurableSet_layer ε)
    fun _ _ => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_of_continuous (by fun_prop) (layer_subset_closedBall ε))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_sphere_of_continuous (F := fun x => f x ^ 2) (by fun_prop))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_of_continuous (F := fun x => ‖∇ f x‖ ^ 2) (by fun_prop)
        (layer_subset_closedBall ε))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-! ### Sobolev bookkeeping for the cutoff decomposition -/

theorem continuous_norm_gradient (g : SmoothData) : Continuous fun x => ‖∇ g.1 x‖ := by
  have := g.2.continuous_fderiv (n := ∞) (by simp)
  simp only [norm_gradient_eq_norm_fderiv]
  fun_prop

/-- `ζ_ε f`, the part of `f` near the sphere. -/
def cutoffData (ε : ℝ) (f : SmoothData) : SmoothData :=
  ⟨fun y => cutoff ε y * f.1 y, (contDiff_cutoff ε).mul f.2⟩

/-- `(1 - ζ_ε) f`, which vanishes on the sphere. -/
def innerData (ε : ℝ) (f : SmoothData) : SmoothData :=
  ⟨fun y => (1 - cutoff ε y) * f.1 y, (contDiff_const.sub (contDiff_cutoff ε)).mul f.2⟩

theorem smoothSobolev_split (ε : ℝ) (f : SmoothData) :
    smoothSobolev f = smoothSobolev (innerData ε f) + smoothSobolev (cutoffData ε f) := by
  apply TauCeti.W1p.ext_value
  have hadd : TauCeti.W1p.value (smoothSobolev (innerData ε f) + smoothSobolev (cutoffData ε f)) =
      TauCeti.W1p.value (smoothSobolev (innerData ε f)) +
        TauCeti.W1p.value (smoothSobolev (cutoffData ε f)) := by
    simp only [← TauCeti.W1p.valueL_apply, map_add]
  rw [hadd]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (TauCeti.W1p.value (smoothSobolev (innerData ε f)))
      (TauCeti.W1p.value (smoothSobolev (cutoffData ε f))),
    value_smoothSobolev_ae f, value_smoothSobolev_ae (innerData ε f),
    value_smoothSobolev_ae (cutoffData ε f)] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, h4]
  simp only [innerData, cutoffData]
  ring

theorem innerData_mem {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (f : SmoothData) :
    smoothSobolev (innerData ε f) ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
  smoothBoundaryZeroClosure_constructive _ fun x hx => by
    simp only [innerData, cutoff_eq_one hε0 hε hx, sub_self, zero_mul]

theorem norm_sq_smoothSobolev (g : SmoothData) :
    ‖smoothSobolev g‖ ^ 2 = (∫ x in (ballOpens : Set R3), g.1 x ^ 2) +
      ∫ x in (ballOpens : Set R3), ‖∇ g.1 x‖ ^ 2 := by
  rw [TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← TauCeti.W1p.integral_value_sq_eq_norm_value_sq,
    ← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  have e1 : ∫ x in (ballOpens : Set R3), TauCeti.W1p.value (smoothSobolev g) x ^ 2 =
      ∫ x in (ballOpens : Set R3), g.1 x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [value_smoothSobolev_ae g] with x hx
    rw [hx]
  have e2 : ∫ x in (ballOpens : Set R3), ‖TauCeti.W1p.gradient (smoothSobolev g) x‖ ^ 2 =
      ∫ x in (ballOpens : Set R3), ‖∇ g.1 x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [gradient_smoothSobolev_ae g] with x hx
    rw [hx]
  rw [e1, e2]

theorem unitBall_subset_closedBall : (ballOpens : Set R3) ⊆ Metric.closedBall (0 : R3) 1 :=
  Metric.ball_subset_closedBall

theorem setIntegral_ball_indicator {F : R3 → ℝ} (ε : ℝ) :
    ∫ x in (ballOpens : Set R3), (layer ε).indicator F x = ∫ x in layer ε, F x := by
  rw [setIntegral_indicator (measurableSet_layer ε),
    inter_eq_right.2 (by simpa using layer_subset_B ε)]

theorem norm_sq_cutoffData_le {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, |deriv Real.smoothTransition t| ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (f : SmoothData) :
    ‖smoothSobolev (cutoffData ε f)‖ ^ 2 ≤
      (1 + 32 * M ^ 2 / ε ^ 2) * (∫ x in layer ε, f.1 x ^ 2) +
        2 * ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 := by
  have hfc : Continuous f.1 := f.2.continuous
  have hgc := continuous_norm_gradient f
  have hcc := continuous_norm_gradient (cutoffData ε f)
  have hζc : Continuous (cutoffData ε f).1 := (cutoffData ε f).2.continuous
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  rw [norm_sq_smoothSobolev]
  have h1 : ∫ x in (ballOpens : Set R3), (cutoffData ε f).1 x ^ 2 ≤
      ∫ x in (ballOpens : Set R3), (layer ε).indicator (fun y => f.1 y ^ 2) x := by
    refine setIntegral_mono_on (integrableOn_of_continuous (by fun_prop) unitBall_subset_closedBall)
      ((integrableOn_of_continuous (F := fun y => f.1 y ^ 2) (by fun_prop)
        unitBall_subset_closedBall).indicator (measurableSet_layer ε)) hB fun x hx => ?_
    have hx' : ‖x‖ < 1 := by simpa [B] using hx
    exact cutoffMul_sq_le hε0 hε f.1 hx'
  have h2 : ∫ x in (ballOpens : Set R3), ‖∇ (cutoffData ε f).1 x‖ ^ 2 ≤
      ∫ x in (ballOpens : Set R3), (layer ε).indicator
        (fun y => 2 * ‖∇ f.1 y‖ ^ 2 + 32 * M ^ 2 / ε ^ 2 * f.1 y ^ 2) x := by
    refine setIntegral_mono_on (integrableOn_of_continuous (by fun_prop) unitBall_subset_closedBall)
      ((integrableOn_of_continuous
        (F := fun y => 2 * ‖∇ f.1 y‖ ^ 2 + 32 * M ^ 2 / ε ^ 2 * f.1 y ^ 2) (by fun_prop)
        unitBall_subset_closedBall).indicator (measurableSet_layer ε)) hB fun x hx => ?_
    have hx' : ‖x‖ < 1 := by simpa [B] using hx
    exact gradient_cutoffMul_sq_le hM0 hM hε0 hε f.1 f.2 hx'
  rw [setIntegral_ball_indicator] at h1 h2
  rw [integral_add, integral_const_mul, integral_const_mul] at h2
  · have e : (1 + 32 * M ^ 2 / ε ^ 2) * (∫ x in layer ε, f.1 x ^ 2) =
        (∫ x in layer ε, f.1 x ^ 2) + 32 * M ^ 2 / ε ^ 2 * ∫ x in layer ε, f.1 x ^ 2 := by ring
    linarith
  · exact (integrableOn_of_continuous (F := fun y => 2 * ‖∇ f.1 y‖ ^ 2) (by fun_prop)
      (layer_subset_closedBall ε))
  · exact (integrableOn_of_continuous (F := fun y => 32 * M ^ 2 / ε ^ 2 * f.1 y ^ 2)
      (by fun_prop) (layer_subset_closedBall ε))

/-! ### Norm identifications -/

/-- The gradient of a `W^{1,2}(B)` function, restricted to the boundary layer. -/
def layerGrad (ε : ℝ) : BallH1 →L[ℝ]
    Lp R3 2 (((volume : Measure R3).restrict ballOpens).restrict (layer ε)) :=
  (LpToLpRestrictCLM R3 R3 ℝ ((volume : Measure R3).restrict ballOpens) 2 (layer ε)).comp
    TauCeti.W1p.gradientL

theorem norm_sq_layerGrad (ε : ℝ) (u : BallH1) :
    ‖layerGrad ε u‖ ^ 2 = ∫ x in layer ε, ‖TauCeti.W1p.gradient u x‖ ^ 2
      ∂((volume : Measure R3).restrict ballOpens) := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [LpToLpRestrictCLM_coeFn (𝕜 := ℝ) (layer ε) (TauCeti.W1p.gradient u)] with x hx
  simp only [layerGrad, ContinuousLinearMap.coe_comp, Function.comp_apply,
    TauCeti.W1p.gradientL_apply, hx]

theorem norm_sq_layerGrad_smooth (ε : ℝ) (f : SmoothData) :
    ‖layerGrad ε (smoothSobolev f)‖ ^ 2 = ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 := by
  rw [norm_sq_layerGrad]
  have hres : ((volume : Measure R3).restrict ballOpens).restrict (layer ε) =
      (volume : Measure R3).restrict (layer ε) := by
    rw [Measure.restrict_restrict (measurableSet_layer ε),
      inter_eq_left.2 (by simpa using layer_subset_B ε)]
  have hae := ae_restrict_of_ae_restrict_of_subset (μ := (volume : Measure R3))
    (show layer ε ⊆ (ballOpens : Set R3) by simpa using layer_subset_B ε)
    (gradient_smoothSobolev_ae f)
  rw [hres]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem tendsto_norm_sq_layerGrad (u : BallH1) :
    Tendsto (fun n : ℕ => ‖layerGrad (1 / ((n : ℝ) + 2)) u‖ ^ 2) atTop (𝓝 0) := by
  simp only [norm_sq_layerGrad]
  have hB : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have hint := TauCeti.W1p.integrable_norm_gradient_sq u
  have key : Tendsto (fun n : ℕ => ∫ x, (layer (1 / ((n : ℝ) + 2))).indicator
      (fun x => ‖TauCeti.W1p.gradient u x‖ ^ 2) x ∂((volume : Measure R3).restrict ballOpens))
      atTop (𝓝 (∫ _x, (0 : ℝ) ∂((volume : Measure R3).restrict ballOpens))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖TauCeti.W1p.gradient u x‖ ^ 2)
      (fun n => hint.aestronglyMeasurable.indicator (measurableSet_layer _)) hint
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _)]
      exact indicator_le_self' (fun _ _ => sq_nonneg _) x
    · filter_upwards [ae_restrict_mem hB] with x hx
      have hx' : ‖x‖ < 1 := by simpa [B] using hx
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < 1 - ‖x‖ by linarith)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [indicator_of_notMem]
      intro hmem
      have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have := hmem.1
      linarith
  simp only [integral_zero] at key
  refine key.congr fun n => ?_
  rw [integral_indicator (measurableSet_layer _)]

theorem integral_sphere_eq_trace (τ0 : UnitBallValueTrace) (f : SmoothData) :
    ∫ w : UnitSphere, f.1 w ^ 2 ∂surfaceMeasure =
      (surfaceMeasure univ).toReal * ‖τ0.valueTraceL (smoothSobolev f)‖ ^ 2 := by
  rw [τ0.valueTrace_smooth, ← Lp.integral_norm_sq_eq_norm_sq]
  have hae := ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ)
    (smoothSphereValue f)
  have e : ∫ w, ‖(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f) w‖ ^ 2
      ∂sphereProbability = ∫ w : UnitSphere, f.1 w ^ 2 ∂sphereProbability := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [hw, Real.norm_eq_abs, sq_abs]
    rfl
  rw [e, sphereProbability, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, ← mul_assoc,
    mul_inv_cancel₀, one_mul]
  exact ENNReal.toReal_ne_zero.2 ⟨Measure.measure_univ_ne_zero.2 surfaceMeasure_ne_zero, measure_ne_top _ _⟩

/-- The distance bound to `H¹₀` for smooth data. -/
theorem infDist_sq_le_smooth (τ0 : UnitBallValueTrace) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ K : ℝ, ∀ f : SmoothData,
      Metric.infDist (smoothSobolev f)
          (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1) ^ 2 ≤
        K * ‖τ0.valueTraceL (smoothSobolev f)‖ ^ 2 +
          C * ‖layerGrad ε (smoothSobolev f)‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_deriv_smoothTransition_bound
  refine ⟨6 + 512 * M ^ 2, fun ε hε0 hε => ⟨(1 + 32 * M ^ 2 / ε ^ 2) * (2 * ε) *
    (surfaceMeasure univ).toReal, fun f => ?_⟩⟩
  have hε1 : ε ≤ 1 := by linarith
  have hdist : Metric.infDist (smoothSobolev f)
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1) ≤
      ‖smoothSobolev (cutoffData ε f)‖ := by
    refine (Metric.infDist_le_dist_of_mem (innerData_mem hε0 hε1 f)).trans_eq ?_
    rw [dist_eq_norm, smoothSobolev_split ε f, add_sub_cancel_left]
  have hsq := pow_le_pow_left₀ Metric.infDist_nonneg hdist 2
  have hc := norm_sq_cutoffData_le hM0 hM hε0 hε1 f
  have hh := hardy_layer f.1 f.2 hε0 hε
  rw [integral_sphere_eq_trace τ0 f] at hh
  rw [norm_sq_layerGrad_smooth]
  have hI0 : 0 ≤ ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 := setIntegral_nonneg (measurableSet_layer ε)
    fun _ _ => sq_nonneg _
  have hc0 : 0 ≤ 1 + 32 * M ^ 2 / ε ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hh hc0
  have e : (1 + 32 * M ^ 2 / ε ^ 2) * (16 * ε ^ 2) = 16 * ε ^ 2 + 512 * M ^ 2 := by
    field_simp; ring
  have h4 : (16 * ε ^ 2 + 512 * M ^ 2) * ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 ≤
      (4 + 512 * M ^ 2) * ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hI0
    nlinarith
  calc _ ≤ _ := hsq
    _ ≤ _ := hc
    _ ≤ _ := by
      have e2 : (1 + 32 * M ^ 2 / ε ^ 2) * (16 * ε ^ 2 * ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2) =
          (16 * ε ^ 2 + 512 * M ^ 2) * ∫ x in layer ε, ‖∇ f.1 x‖ ^ 2 := by
        rw [← mul_assoc, e]
      linarith

end OAI.AnisotropicCalderon.TraceKernel
