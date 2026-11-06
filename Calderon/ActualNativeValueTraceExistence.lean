import Calderon.NativeValueRadialTrace
import Calderon.NativeGlobalSmoothH1Density
import Calderon.CollaboratorTraceKernelHelpersOct17
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily SphereHarmonic TraceKernel

/-! ### One-dimensional endpoint estimate on `[1/2, 1]` -/

/-- Fundamental theorem of calculus for `(r - a) * g r ^ 2` on `[a, 1]`. -/
theorem valueTrace_endpoint_identity {g g' : ℝ → ℝ} (hg : ∀ r, HasDerivAt g (g' r) r)
    (hg' : Continuous g') (a : ℝ) :
    ∫ r in a..1, (g r ^ 2 + 2 * (r - a) * g r * g' r) = (1 - a) * g 1 ^ 2 := by
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
  exact hFint

/-- `g(1)^2 ≤ ∫_{1/2}^1 r^2 (16 g^2 + 2 G^2)` whenever `g'^2 ≤ G^2`. -/
theorem valueTrace_endpoint_sq_le {g g' G : ℝ → ℝ} (hg : ∀ r, HasDerivAt g (g' r) r)
    (hg' : Continuous g') (hG : Continuous G) (hgG : ∀ r, g' r ^ 2 ≤ G r ^ 2) :
    g 1 ^ 2 ≤ ∫ r in (1 / 2 : ℝ)..1, r ^ 2 * (16 * g r ^ 2 + 2 * G r ^ 2) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun r => (hg r).continuousAt
  have ha : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hid := valueTrace_endpoint_identity hg hg' (1 / 2)
  have hmono : ∫ r in (1 / 2 : ℝ)..1, (g r ^ 2 + 2 * (r - 1 / 2) * g r * g' r) ≤
      ∫ r in (1 / 2 : ℝ)..1, (1 / 2) * (r ^ 2 * (16 * g r ^ 2 + 2 * G r ^ 2)) := by
    refine intervalIntegral.integral_mono_on ha
      ((by fun_prop : Continuous fun r : ℝ =>
        g r ^ 2 + 2 * (r - 1 / 2) * g r * g' r).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun r : ℝ =>
        (1 / 2) * (r ^ 2 * (16 * g r ^ 2 + 2 * G r ^ 2))).intervalIntegrable _ _) ?_
    intro r hr
    have h0 : 0 ≤ r - 1 / 2 := by linarith [hr.1]
    have h1 : r - 1 / 2 ≤ 1 / 2 := by linarith [hr.2]
    have hr2 : 1 / 4 ≤ r ^ 2 := by nlinarith [hr.1]
    have hsq : (r - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
    -- exact certificate:
    -- RHS - LHS = (g - (r-1/2) g')^2 + 8 (r^2-1/4) g^2 + (1/4-(r-1/2)^2) g'^2
    --             + (r^2-1/4) G^2 + (1/4) (G^2 - g'^2)
    nlinarith [sq_nonneg (g r - (r - 1 / 2) * g' r),
      mul_nonneg (sub_nonneg.2 hr2) (sq_nonneg (g r)),
      mul_nonneg (sub_nonneg.2 hsq) (sq_nonneg (g' r)),
      mul_nonneg (sub_nonneg.2 hr2) (sq_nonneg (G r)), hgG r]
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith

/-! ### Ray estimate and polar integration -/

/-- The endpoint estimate along the ray through a unit vector `w`. -/
theorem valueTrace_sphere_sq_le_radial (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (w : R3)
    (hw : ‖w‖ = 1) :
    f w ^ 2 ≤ ∫ r in Ioo (1 - (1 / 2 : ℝ)) 1,
      r ^ 2 * (16 * f (r • w) ^ 2 + 2 * ‖∇ f (r • w)‖ ^ 2) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => f (r • w)) (fderiv ℝ f (r • w) w) r := by
    intro r
    have := ((hf.differentiable (by simp)) (r • w)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const w)
    rw [one_smul] at this
    exact this
  have hray : Continuous fun r : ℝ => r • w :=
    (continuous_id.smul continuous_const : Continuous fun r : ℝ => r • w)
  have hdc : Continuous fun r : ℝ => fderiv ℝ f (r • w) w := by
    first
    | exact ((hf.continuous_fderiv (by simp)).comp hray).clm_apply continuous_const
    | (have := hf.continuous_fderiv (n := ∞) (by simp); fun_prop)
  have hgc : Continuous fun r : ℝ => ‖∇ f (r • w)‖ := by
    first
    | exact (continuous_norm_gradient ⟨f, hf⟩).comp hray
    | (have := hf.continuous_fderiv (n := ∞) (by simp)
       simp only [norm_gradient_eq_norm_fderiv]
       fun_prop)
  have hgG : ∀ r : ℝ, fderiv ℝ f (r • w) w ^ 2 ≤ ‖∇ f (r • w)‖ ^ 2 := by
    intro r
    have hle : |fderiv ℝ f (r • w) w| ≤ ‖∇ f (r • w)‖ := by
      rw [norm_gradient_eq_norm_fderiv, ← Real.norm_eq_abs]
      simpa [hw] using (fderiv ℝ f (r • w)).le_opNorm w
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  have h := valueTrace_endpoint_sq_le (g := fun r : ℝ => f (r • w))
    (g' := fun r : ℝ => fderiv ℝ f (r • w) w) (G := fun r : ℝ => ‖∇ f (r • w)‖)
    hd hdc hgc hgG
  have hIoo : ∫ r in Ioo (1 - (1 / 2 : ℝ)) 1,
      r ^ 2 * (16 * f (r • w) ^ 2 + 2 * ‖∇ f (r • w)‖ ^ 2) =
      ∫ r in (1 / 2 : ℝ)..1, r ^ 2 * (16 * f (r • w) ^ 2 + 2 * ‖∇ f (r • w)‖ ^ 2) := by
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num,
      intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [hIoo]
  simpa only [one_smul] using h

/-- Surface `L²` mass of a smooth datum is bounded by the boundary-layer energy. -/
theorem valueTrace_integral_sphere_sq_le_layer (f : SmoothData) :
    ∫ w : UnitSphere, f.1 w ^ 2 ∂surfaceMeasure ≤
      ∫ x in layer (1 / 2), (16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) := by
  have hfc : Continuous f.1 := f.2.continuous
  have hgc : Continuous fun x => ‖∇ f.1 x‖ := continuous_norm_gradient f
  have hGc : Continuous fun x => 16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2 :=
    (continuous_const.mul (hfc.pow 2)).add (continuous_const.mul (hgc.pow 2))
  have hG0 : ∀ x, 0 ≤ 16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2 := fun x => by positivity
  have hl : ∫⁻ w : UnitSphere, ENNReal.ofReal (f.1 w ^ 2) ∂surfaceMeasure ≤
      ∫⁻ x in layer (1 / 2), ENNReal.ofReal (16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) := by
    rw [lintegral_layer_eq (fun x => 16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) hGc hG0
      (by norm_num : (1 / 2 : ℝ) < 1)]
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    exact valueTrace_sphere_sq_le_radial f.1 f.2 w (norm_eq_of_mem_sphere w)
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_sphere_of_continuous (F := fun x => f.1 x ^ 2) (hfc.pow 2))
      (Eventually.of_forall fun _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_of_continuous hGc (layer_subset_closedBall (1 / 2)))
      (Eventually.of_forall fun x => hG0 x)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff
    (setIntegral_nonneg (measurableSet_layer _) fun x _ => hG0 x)).1 hl

/-- Uniform surface bound by the SAME native `BallH1` norm. -/
theorem valueTrace_integral_sphere_sq_le_native (f : SmoothData) :
    ∫ w : UnitSphere, f.1 w ^ 2 ∂surfaceMeasure ≤ 16 * ‖smoothSobolev f‖ ^ 2 := by
  have hfc : Continuous f.1 := f.2.continuous
  have hgc : Continuous fun x => ‖∇ f.1 x‖ := continuous_norm_gradient f
  have hc1 : Continuous fun x => 16 * f.1 x ^ 2 := continuous_const.mul (hfc.pow 2)
  have hc2 : Continuous fun x => 2 * ‖∇ f.1 x‖ ^ 2 := continuous_const.mul (hgc.pow 2)
  have hGc : Continuous fun x => 16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2 := hc1.add hc2
  have hG0 : ∀ x, 0 ≤ 16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2 := fun x => by positivity
  have hlayer : layer (1 / 2) ⊆ (ballOpens : Set R3) := by simpa using layer_subset_B (1 / 2)
  have hmono : ∫ x in layer (1 / 2), (16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) ≤
      ∫ x in (ballOpens : Set R3), (16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) :=
    setIntegral_mono_set (integrableOn_of_continuous hGc unitBall_subset_closedBall)
      (Eventually.of_forall fun x => hG0 x) (LE.le.eventuallySubset hlayer)
  have hsplit : ∫ x in (ballOpens : Set R3), (16 * f.1 x ^ 2 + 2 * ‖∇ f.1 x‖ ^ 2) =
      16 * (∫ x in (ballOpens : Set R3), f.1 x ^ 2) +
        2 * ∫ x in (ballOpens : Set R3), ‖∇ f.1 x‖ ^ 2 := by
    rw [integral_add, integral_const_mul, integral_const_mul]
    · exact integrableOn_of_continuous hc1 unitBall_subset_closedBall
    · exact integrableOn_of_continuous hc2 unitBall_subset_closedBall
  have hsph := valueTrace_integral_sphere_sq_le_layer f
  have hn := norm_sq_smoothSobolev f
  have hI0 : 0 ≤ ∫ x in (ballOpens : Set R3), ‖∇ f.1 x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  linarith

/-- Elementary probability-normalization identity (no trace witness involved). -/
theorem valueTrace_sq_norm_toLp_smoothSphereValue (f : SmoothData) :
    ‖(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)‖ ^ 2 =
      (surfaceMeasure univ).toReal⁻¹ * ∫ w : UnitSphere, f.1 w ^ 2 ∂surfaceMeasure := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have hae := ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ)
    (smoothSphereValue f)
  have e : ∫ w, ‖(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f) w‖ ^ 2
      ∂sphereProbability = ∫ w : UnitSphere, f.1 w ^ 2 ∂sphereProbability := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [hw, Real.norm_eq_abs, sq_abs]
    rfl
  rw [e, sphereProbability, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]

/-- Scalar homogeneity of the native smooth jet. -/
theorem valueTrace_smoothSobolev_smul (c : ℝ) (f : SmoothData) :
    smoothSobolev ⟨c • f.1, f.2.const_smul c⟩ = c • smoothSobolev f := by
  apply TauCeti.W1p.ext_value
  simp only [← TauCeti.W1p.valueL_apply, map_smul]
  simp only [TauCeti.W1p.valueL_apply, value_smoothSobolev]
  exact MemLp.toLp_const_smul c (memLp_smooth_value f)

theorem exists_smoothSphereValue_uniform_native_H1_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SmoothData,
      ‖(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)‖ ≤
        C * ‖smoothSobolev f‖ := by
  have ht0 : 0 ≤ (surfaceMeasure univ).toReal⁻¹ := inv_nonneg.2 ENNReal.toReal_nonneg
  refine ⟨4 * ((surfaceMeasure univ).toReal⁻¹ + 1), by linarith, fun f => ?_⟩
  have hnorm := valueTrace_sq_norm_toLp_smoothSphereValue f
  have hI := valueTrace_integral_sphere_sq_le_native f
  have h1 := mul_le_mul_of_nonneg_left hI ht0
  have hN := norm_nonneg (smoothSobolev f)
  have hT := norm_nonneg ((ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f))
  have hsq : ‖(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)‖ ^ 2 ≤
      (4 * ((surfaceMeasure univ).toReal⁻¹ + 1) * ‖smoothSobolev f‖) ^ 2 := by
    rw [hnorm]
    nlinarith [mul_nonneg (sq_nonneg (surfaceMeasure univ).toReal⁻¹)
        (sq_nonneg ‖smoothSobolev f‖),
      mul_nonneg ht0 (sq_nonneg ‖smoothSobolev f‖), sq_nonneg ‖smoothSobolev f‖]
  have hc : 0 ≤ 4 * ((surfaceMeasure univ).toReal⁻¹ + 1) * ‖smoothSobolev f‖ :=
    mul_nonneg (by linarith) hN
  nlinarith [hsq, hc, hT]

theorem nonempty_unitBallValueTrace : Nonempty UnitBallValueTrace := by
  obtain ⟨C, -, hC⟩ := exists_smoothSphereValue_uniform_native_H1_bound
  -- the local module of globally smooth ambient functions
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ (R3 → ℝ), ∀ g : R3 → ℝ, g ∈ W ↔ ContDiff ℝ ∞ g :=
    ⟨{ carrier := {g | ContDiff ℝ ∞ g}
       add_mem' := by
         intro a b ha hb
         show ContDiff ℝ ∞ (a + b)
         exact (show ContDiff ℝ ∞ a from ha).add (show ContDiff ℝ ∞ b from hb)
       zero_mem' := by
         show ContDiff ℝ ∞ (0 : R3 → ℝ)
         exact (contDiff_const : ContDiff ℝ ∞ fun _ : R3 => (0 : ℝ))
       smul_mem' := by
         intro c a ha
         show ContDiff ℝ ∞ (c • a)
         exact (show ContDiff ℝ ∞ a from ha).const_smul c }, fun _ => Iff.rfl⟩
  -- the native jet map on smooth data
  obtain ⟨e, he⟩ : ∃ e : W →ₗ[ℝ] BallH1, ∀ w : W,
      e w = smoothSobolev ⟨w.1, (hW w.1).1 w.2⟩ :=
    ⟨{ toFun := fun w => smoothSobolev ⟨w.1, (hW w.1).1 w.2⟩
       map_add' := fun u v => smoothSobolev_add ⟨u.1, (hW u.1).1 u.2⟩ ⟨v.1, (hW v.1).1 v.2⟩
       map_smul' := fun c u => valueTrace_smoothSobolev_smul c ⟨u.1, (hW u.1).1 u.2⟩ },
      fun _ => rfl⟩
  -- the actual restriction to the unit sphere
  obtain ⟨S, hS⟩ : ∃ S : W →ₗ[ℝ] C(UnitSphere, ℝ), ∀ w : W,
      S w = smoothSphereValue ⟨w.1, (hW w.1).1 w.2⟩ :=
    ⟨{ toFun := fun w => smoothSphereValue ⟨w.1, (hW w.1).1 w.2⟩
       map_add' := fun u v => by
         ext x
         first
         | rfl
         | simp [smoothSphereValue]
       map_smul' := fun c u => by
         ext x
         first
         | rfl
         | simp [smoothSphereValue] }, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : W →ₗ[ℝ] SphereL2, ∀ w : W,
      T w = (ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothSphereValue ⟨w.1, (hW w.1).1 w.2⟩) :=
    ⟨((ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere, ℝ) →L[ℝ] SphereL2) :
        C(UnitSphere, ℝ) →ₗ[ℝ] SphereL2).comp S,
      fun w => (congrArg
        (ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere, ℝ) →L[ℝ] SphereL2)
        (hS w) :)⟩
  have hbound : ∀ w : W, ‖T w‖ ≤ C * ‖e w‖ := fun w => by
    rw [hT, he]
    exact hC _
  have hdense : DenseRange e := by
    refine Dense.mono ?_ denseRange_smoothSobolev
    rintro _ ⟨g, rfl⟩
    exact ⟨⟨g.1, (hW g.1).2 g.2⟩, he _⟩
  exact ⟨{ valueTraceL := T.extendOfNorm e
           valueTrace_smooth := fun g => by
             have h1 := LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ ⟨g.1, (hW g.1).2 g.2⟩
             rw [he, hT] at h1
             exact h1 }⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
