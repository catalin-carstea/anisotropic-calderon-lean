import Calderon.CollaboratorRotationSobolevOct17
import TauCeti.Analysis.Sobolev.W1p.MeyersSerrin
import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Rotational derivatives of `H² ∩ H¹₀(B)` functions lie in `H¹₀(B)` (helper for task 05).

Proof outline: for `θ > 0` the difference quotients `θ⁻¹ (v ∘ R_θ - v)` lie in `H¹₀(B)`.  For any
`u ∈ L²(B; F)` with weak derivative `U` and `w = U(·)(gen ·) ∈ L²`, the identity
`u ∘ R_θ - u = ∫₀^θ w ∘ R_t dt` holds in `L²(B; F)` (tested against test functions, using the weak
derivative along the generator and Fubini), and strong continuity of rotations on `L²` gives
`θ⁻¹ (u ∘ R_θ - u) → w`.  Applied to `v` and to `∇v` (using the `H²` structure), the difference
quotients are Cauchy in `W^{1,2}(B)`; their limit lies in the closed subspace `H¹₀(B)` and has
value `⟪gen, ∇v⟫`. -/

noncomputable section
open MeasureTheory TopologicalSpace Filter Topology
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.Rotation
open TauCeti EnergyBridge BoundedContinuousFunction

theorem isFiniteMeasure_ballRestrict :
    IsFiniteMeasure ((volume : Measure R3).restrict ballOpens) :=
  isFiniteMeasure_restrict.2 (by
    simpa only [coe_ballOpens, B] using (measure_ball_lt_top (μ := (volume : Measure R3))
      (x := 0) (r := 1)).ne)

attribute [instance] isFiniteMeasure_ballRestrict

set_option linter.unusedSectionVars false
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable (F) in
/-- Precomposition with `rot θ` on `L²(B; F)`. -/
def rotLp (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) :
    Lp F 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp F 2 ((volume : Measure R3).restrict ballOpens) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (rot j k hjk θ)
    (measurePreserving_rot_ball j k hjk θ)).toContinuousLinearMap

theorem rotLp_ae (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    ⇑(rotLp F j k hjk θ f) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => f (rot j k hjk θ x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem norm_rotLp (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    ‖rotLp F j k hjk θ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem rotLp_rotLp (j k : Fin 3) (hjk : j ≠ k) (r s : ℝ)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    rotLp F j k hjk s (rotLp F j k hjk r f) = rotLp F j k hjk (r + s) f := by
  apply Lp.ext
  have hq := (measurePreserving_rot_ball j k hjk s).quasiMeasurePreserving.tendsto_ae
  filter_upwards [rotLp_ae j k hjk s (rotLp F j k hjk r f),
    hq.eventually (rotLp_ae j k hjk r f), rotLp_ae j k hjk (r + s) f] with x h1 h2 h3
  rw [h1, h2, h3, rot_add]

theorem rotLp_zero (j k : Fin 3) (hjk : j ≠ k)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    rotLp F j k hjk 0 f = f := by
  apply Lp.ext
  filter_upwards [rotLp_ae j k hjk 0 f] with x h
  rw [h, rot_zero]


/-- Uniform closeness of a bounded continuous function and its rotation on the ball. -/
theorem eventually_norm_rotLp_toLp_sub_le (j k : Fin 3) (hjk : j ≠ k) (g : R3 →ᵇ F)
    (hg : MemLp g 2 ((volume : Measure R3).restrict ballOpens)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝 (0:ℝ), ‖rotLp F j k hjk t (hg.toLp g) - hg.toLp g‖ ≤
      (measureUnivNNReal ((volume : Measure R3).restrict ballOpens) : ℝ) ^
        (2 : ENNReal).toReal⁻¹ * δ := by
  have hcont : ContinuousOn (fun z : ℝ × R3 => g (rot j k hjk z.1 z.2))
      (Set.univ ×ˢ Metric.closedBall (0 : R3) 1) :=
    (g.continuous.comp ((continuous_rot_uncurry j k hjk).comp continuous_swap)).continuousOn
  obtain ⟨V, hV, hVu⟩ := (isCompact_closedBall (0 : R3) 1).mem_uniformity_of_prod
    (f := fun t x => g (rot j k hjk t x)) hcont (Set.mem_univ (0:ℝ))
    (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hV
  filter_upwards [hV] with t ht
  apply Lp.norm_le_of_ae_bound hδ.le
  have hq := (measurePreserving_rot_ball j k hjk t).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_sub (rotLp F j k hjk t (hg.toLp g)) (hg.toLp g),
    rotLp_ae j k hjk t (hg.toLp g), hq.eventually hg.coeFn_toLp, hg.coeFn_toLp,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x h1 h2 h3 h4 hx
  rw [h1, Pi.sub_apply, h2, h3, h4]
  have hxb : x ∈ Metric.closedBall (0 : R3) 1 :=
    Metric.ball_subset_closedBall (by simpa [B] using hx)
  have := hVu t ht x hxb
  simp only [Set.mem_ofPred_eq, rot_zero] at this
  rw [← dist_eq_norm]
  exact this.le

theorem tendsto_rotLp (j k : Fin 3) (hjk : j ≠ k)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    Tendsto (fun t => rotLp F j k hjk t f) (𝓝 0) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := (measureUnivNNReal ((volume : Measure R3).restrict ballOpens) : ℝ) ^
    (2 : ENNReal).toReal⁻¹ with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨g, hg1, hg2⟩ := MemLp.exists_boundedContinuous_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (MeasureTheory.Lp.memLp f) (ε := ENNReal.ofReal (ε / 4)) (by simp [hε])
  have hfg : ‖f - hg2.toLp g‖ ≤ ε / 4 := by
    rw [Lp.norm_def]
    have : eLpNorm (⇑(f - hg2.toLp g)) 2 ((volume : Measure R3).restrict ballOpens) =
        eLpNorm (⇑f - ⇑g) 2 ((volume : Measure R3).restrict ballOpens) := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub f (hg2.toLp g), hg2.coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, h2]; rfl
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hg1
  have hδ : 0 < ε / (4 * (M + 1)) := by positivity
  filter_upwards [eventually_norm_rotLp_toLp_sub_le j k hjk g hg2 hδ] with t ht
  rw [dist_eq_norm]
  have hMδ : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e1 : rotLp F j k hjk t f - f = rotLp F j k hjk t (f - hg2.toLp g) +
      (rotLp F j k hjk t (hg2.toLp g) - hg2.toLp g) + (hg2.toLp g - f) := by
    rw [map_sub]; abel
  rw [e1]
  calc _ ≤ ‖rotLp F j k hjk t (f - hg2.toLp g)‖ +
        ‖rotLp F j k hjk t (hg2.toLp g) - hg2.toLp g‖ + ‖hg2.toLp g - f‖ := norm_add₃_le
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by
        rw [norm_rotLp, norm_sub_rev (hg2.toLp g)]
        gcongr
        exact ht.trans hMδ
    _ < ε := by linarith

theorem continuous_rotLp (j k : Fin 3) (hjk : j ≠ k)
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    Continuous fun t => rotLp F j k hjk t f := by
  rw [continuous_iff_continuousAt]
  intro s
  have h : (fun t => rotLp F j k hjk t f) =
      fun t => rotLp F j k hjk s (rotLp F j k hjk (t - s) f) := by
    funext t; rw [rotLp_rotLp, sub_add_cancel]
  have h2 : Tendsto (fun t : ℝ => t - s) (𝓝 s) (𝓝 0) := by
    simpa using (continuous_id.sub continuous_const).tendsto s (f := fun t : ℝ => t - s)
  rw [ContinuousAt, h]
  exact ((rotLp F j k hjk s).continuous.tendsto f).comp ((tendsto_rotLp j k hjk f).comp h2)


open scoped Distributions ContDiff

/-- Pairing of `L²(B; F)` against a scalar test function. -/
def pairL (ψ : 𝓓(ballOpens, ℝ)) : Lp F 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] F :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing ((volume : Measure R3).restrict ballOpens) 2 2
    (testFunctionLp (mu := (volume : Measure R3)) 2 ψ)

theorem pairL_apply (ψ : 𝓓(ballOpens, ℝ)) (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    pairL ψ f = ∫ x, ψ x • f x ∂((volume : Measure R3).restrict ballOpens) := by
  rw [pairL, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [hx]

theorem eq_zero_of_integral_testFunction_smul
    (g : Lp F 2 ((volume : Measure R3).restrict ballOpens))
    (h : ∀ ψ : 𝓓(ballOpens, ℝ), ∫ x, ψ x • g x ∂((volume : Measure R3).restrict ballOpens) = 0) :
    g = 0 := by
  apply Lp.ext
  have hzero : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), g x = 0 := by
    rw [ae_restrict_iff' ballOpens.isOpen.measurableSet]
    refine ballOpens.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((MeasureTheory.Lp.memLp g).locallyIntegrable (by simp))) fun φ hφ hφc hφs => ?_
    let ψ : 𝓓(ballOpens, ℝ) := ⟨φ, hφ, hφc, hφs⟩
    rw [← h ψ]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
    simp [this]
  exact Filter.EventuallyEq.trans hzero (Lp.coeFn_zero F 2 _).symm

/-! ### The generator -/

theorem gen_apply_j (j k : Fin 3) (hjk : j ≠ k) (x : R3) : gen j k x j = - x k := by
  simp [gen, hjk]

theorem gen_apply_k (j k : Fin 3) (hjk : j ≠ k) (x : R3) : gen j k x k = x j := by
  simp [gen, hjk.symm]

theorem gen_apply_other (j k : Fin 3) (x : R3) (m : Fin 3) (hmj : m ≠ j) (hmk : m ≠ k) :
    gen j k x m = 0 := by
  simp [gen, hmj, hmk]

theorem rot_gen (j k : Fin 3) (hjk : j ≠ k) (s : ℝ) (x : R3) :
    rot j k hjk s (gen j k x) = gen j k (rot j k hjk s x) := by
  ext m
  by_cases hmj : m = j
  · subst hmj; simp only [rot_apply_j, rot_apply_k, gen_apply_j _ _ hjk, gen_apply_k _ _ hjk]; ring
  by_cases hmk : m = k
  · subst hmk; simp only [rot_apply_j, rot_apply_k, gen_apply_j _ _ hjk, gen_apply_k _ _ hjk]; ring
  rw [rot_apply_other j k hjk _ _ m hmj hmk, gen_apply_other j k _ m hmj hmk,
    gen_apply_other j k _ m hmj hmk]

theorem continuous_gen_field (j k : Fin 3) : Continuous (gen j k) := by
  unfold gen; fun_prop

/-- Multiplication of a test function by a coordinate. -/
def coordMul (m : Fin 3) (φ : 𝓓(ballOpens, ℝ)) : 𝓓(ballOpens, ℝ) :=
  ⟨fun x => x m * φ x, (EuclideanSpace.proj m : R3 →L[ℝ] ℝ).contDiff.mul φ.contDiff,
    φ.hasCompactSupport.mul_left,
    (tsupport_mul_subset_right (f := fun x : R3 => x m)).trans φ.tsupport_subset⟩

theorem coordMul_apply (m : Fin 3) (φ : 𝓓(ballOpens, ℝ)) (x : R3) :
    coordMul m φ x = x m * φ x := rfl

theorem lineDeriv_coordMul (m : Fin 3) (φ : 𝓓(ballOpens, ℝ)) (x v : R3) :
    lineDeriv ℝ (coordMul m φ : R3 → ℝ) x v = x m * fderiv ℝ (φ : R3 → ℝ) x v + v m * φ x := by
  have hφ : HasFDerivAt (φ : R3 → ℝ) (fderiv ℝ (φ : R3 → ℝ) x) x :=
    (φ.contDiff.differentiable (by simp) x).hasFDerivAt
  have hp : HasFDerivAt (fun y : R3 => y m) (EuclideanSpace.proj m : R3 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj m : R3 →L[ℝ] ℝ).hasFDerivAt
  have h := hp.mul hφ
  have h2 := (h.hasLineDerivAt v).lineDeriv
  have hc : (coordMul m φ : R3 → ℝ) = (fun y : R3 => y m) * (φ : R3 → ℝ) := rfl
  rw [hc, h2]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [show (EuclideanSpace.proj m : R3 →L[ℝ] ℝ) v = v m from rfl]
  ring

/-- Weak derivative along the rotation generator. -/
theorem integral_fderiv_gen_smul (j k : Fin 3) (hjk : j ≠ k) {u : R3 → F} {U : R3 → R3 →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ballOpens u U) (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x, fderiv ℝ (φ : R3 → ℝ) x (gen j k x) • u x =
      -∫ x, φ x • U x (gen j k x) := by
  set ek : R3 := EuclideanSpace.single k 1
  set ej : R3 := EuclideanSpace.single j 1
  have h1 := (hu.hasWeakLineDerivOn ek).integral_lineDeriv_smul_eq_neg_integral_smul
    (coordMul j φ)
  have h2 := (hu.hasWeakLineDerivOn ej).integral_lineDeriv_smul_eq_neg_integral_smul
    (coordMul k φ)
  have hl : LocallyIntegrableOn u ballOpens volume := (hu.hasWeakLineDerivOn ek).locallyIntegrableOn
  have hpt : (fun x => fderiv ℝ (φ : R3 → ℝ) x (gen j k x) • u x) = fun x =>
      lineDeriv ℝ (coordMul j φ : R3 → ℝ) x ek • u x -
        lineDeriv ℝ (coordMul k φ : R3 → ℝ) x ej • u x := by
    funext x
    rw [lineDeriv_coordMul, lineDeriv_coordMul, ← sub_smul]
    congr 1
    simp only [gen, map_sub, map_smul, smul_eq_mul, ek, ej, PiLp.single_apply, hjk,
      hjk.symm, ite_false]
    ring
  have hpt2 : (fun x => (φ : R3 → ℝ) x • U x (gen j k x)) = fun x =>
      (coordMul j φ : R3 → ℝ) x • U x ek - (coordMul k φ : R3 → ℝ) x • U x ej := by
    funext x
    simp only [gen, map_sub, map_smul, coordMul_apply, smul_sub, smul_smul, ek, ej]
    rw [mul_comm (x j), mul_comm (x k)]
  rw [hpt, hpt2, integral_sub (integrable_lineDeriv_smul_of_locallyIntegrableOn hl _ _)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hl _ _),
    integral_sub (integrable_smul_of_locallyIntegrableOn
        (hu.hasWeakLineDerivOn ek).locallyIntegrableOn_deriv _)
      (integrable_smul_of_locallyIntegrableOn
        (hu.hasWeakLineDerivOn ej).locallyIntegrableOn_deriv _), h1, h2]
  abel


/-! ### The key pairing identity -/

theorem integral_smul_rotLp (j k : Fin 3) (hjk : j ≠ k) (t : ℝ) (ψ : 𝓓(ballOpens, ℝ))
    (f : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    ∫ x, ψ x • rotLp F j k hjk t f x ∂((volume : Measure R3).restrict ballOpens) =
      ∫ x, ψ (rot j k hjk (-t) x) • f x ∂((volume : Measure R3).restrict ballOpens) := by
  calc _ = ∫ x, ψ x • f (rot j k hjk t x) ∂((volume : Measure R3).restrict ballOpens) := by
        apply integral_congr_ae
        filter_upwards [rotLp_ae j k hjk t f] with x h
        rw [h]
    _ = ∫ x, (fun y => ψ (rot j k hjk (-t) y) • f y) (rot j k hjk t x)
          ∂((volume : Measure R3).restrict ballOpens) := by
        congr 1; funext x; simp only [rot_add, neg_add_cancel, rot_zero]
    _ = _ := setIntegral_ball_comp_rot j k hjk t (fun y => ψ (rot j k hjk (-t) y) • f y)

/-- The derivative integrand `a ψ t x = -Dψ(R_{-t} x)(gen (R_{-t} x))`. -/
def derivInt (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) (t : ℝ) (x : R3) : ℝ :=
  -fderiv ℝ (ψ : R3 → ℝ) (rot j k hjk (-t) x) (gen j k (rot j k hjk (-t) x))

theorem continuous_derivInt (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) :
    Continuous fun z : R3 × ℝ => derivInt j k hjk ψ z.2 z.1 := by
  have hr : Continuous fun z : R3 × ℝ => rot j k hjk (-z.2) z.1 := by
    simp only [rot_apply_formula]
    fun_prop
  have h1 : Continuous (fderiv ℝ (ψ : R3 → ℝ)) := ψ.contDiff.continuous_fderiv (by simp)
  have h2 : Continuous fun z : R3 × ℝ =>
      fderiv ℝ (ψ : R3 → ℝ) (rot j k hjk (-z.2) z.1) (gen j k (rot j k hjk (-z.2) z.1)) :=
    Continuous.clm_apply (h1.comp hr) ((continuous_gen_field j k).comp hr)
  exact h2.neg

theorem abs_derivInt_le (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) :
    ∃ C, 0 ≤ C ∧ ∀ t x, ‖derivInt j k hjk ψ t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (continuous_gradient_testFunction ψ).bounded_above_of_compact_support
    (hasCompactSupport_gradient_testFunction ψ)
  refine ⟨max C 0, le_max_right _ _, fun t x => ?_⟩
  rw [derivInt, norm_neg]
  exact (norm_fderiv_apply_gen_le j k hjk ψ _).trans ((hC _).trans (le_max_left _ _))

theorem hasDerivAt_testFunction_rot (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) (x : R3)
    (t : ℝ) : HasDerivAt (fun t => ψ (rot j k hjk (-t) x)) (derivInt j k hjk ψ t x) t := by
  have hr : HasDerivAt (fun t => rot j k hjk (-t) x) (-gen j k (rot j k hjk (-t) x)) t := by
    have := (hasDerivAt_rot j k hjk (-t) x).scomp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using this
  have := ((ψ.contDiff.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hr
  simp only [map_neg] at this
  exact this

theorem testFunction_rot_sub (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ)) (θ : ℝ) (x : R3) :
    ψ (rot j k hjk (-θ) x) - ψ x = ∫ t in (0:ℝ)..θ, derivInt j k hjk ψ t x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_testFunction_rot j k hjk ψ x t)]
  · simp [rot_zero]
  · exact ((continuous_derivInt j k hjk ψ).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem integral_integral_derivInt_swap (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ))
    {θ : ℝ} (hθ : 0 ≤ θ) (u : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    ∫ x, (∫ t in (0:ℝ)..θ, derivInt j k hjk ψ t x) • u x
        ∂((volume : Measure R3).restrict ballOpens) =
      ∫ t in (0:ℝ)..θ, ∫ x, derivInt j k hjk ψ t x • u x
        ∂((volume : Measure R3).restrict ballOpens) := by
  have hu : Integrable (⇑u) ((volume : Measure R3).restrict ballOpens) :=
    (MeasureTheory.Lp.memLp u).integrable one_le_two
  obtain ⟨C, hC0, hC⟩ := abs_derivInt_le j k hjk ψ
  simp_rw [← intervalIntegral.integral_smul_const]
  rw [intervalIntegral.integral_of_le hθ]
  simp_rw [intervalIntegral.integral_of_le hθ]
  apply integral_integral_swap
  refine Integrable.mono' ((hu.norm.comp_fst (volume.restrict (Set.Ioc 0 θ))).const_mul C) ?_ ?_
  · exact ((continuous_derivInt j k hjk ψ).aestronglyMeasurable).smul
      (hu.aestronglyMeasurable.comp_fst)
  · filter_upwards with z
    show ‖derivInt j k hjk ψ z.2 z.1 • u z.1‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)


theorem integral_derivInt_smul (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ))
    {u w : Lp F 2 ((volume : Measure R3).restrict ballOpens)} {U : R3 → R3 →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ballOpens (⇑u) U)
    (hw : ⇑w =ᵐ[(volume : Measure R3).restrict ballOpens] fun x => U x (gen j k x)) (t : ℝ) :
    ∫ x, derivInt j k hjk ψ t x • u x ∂((volume : Measure R3).restrict ballOpens) =
      ∫ x, ψ x • rotLp F j k hjk t w x ∂((volume : Measure R3).restrict ballOpens) := by
  set L := rot j k hjk (-t) with hL
  set ψt := compTestFunction L (rot_mem_ball_iff j k hjk (-t)) ψ with hψt
  have hfd : ∀ x, fderiv ℝ (ψt : R3 → ℝ) x (gen j k x) =
      fderiv ℝ (ψ : R3 → ℝ) (L x) (gen j k (L x)) := by
    intro x
    have hd : HasFDerivAt (ψt : R3 → ℝ)
        ((fderiv ℝ (ψ : R3 → ℝ) (L x)).comp (L.toContinuousLinearEquiv : R3 →L[ℝ] R3)) x :=
      ((ψ.contDiff.differentiable (by simp)) (L x)).hasFDerivAt.comp x
        L.toContinuousLinearEquiv.hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply]
    congr 1
    exact rot_gen j k hjk (-t) x
  have hout1 : ∀ x, x ∉ (ballOpens : Set R3) →
      fderiv ℝ (ψt : R3 → ℝ) x (gen j k x) • u x = 0 := by
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ fun h => hx (ψt.tsupport_subset h)]
    simp
  have hout2 : ∀ x, x ∉ (ballOpens : Set R3) → ψt x • U x (gen j k x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (ψt.tsupport_subset h)]
    simp
  calc _ = -∫ x, fderiv ℝ (ψt : R3 → ℝ) x (gen j k x) • u x
          ∂((volume : Measure R3).restrict ballOpens) := by
        rw [← integral_neg]
        congr 1; funext x
        rw [hfd, derivInt, neg_smul]
    _ = -∫ x, fderiv ℝ (ψt : R3 → ℝ) x (gen j k x) • u x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout1]
    _ = ∫ x, ψt x • U x (gen j k x) := by
        rw [integral_fderiv_gen_smul j k hjk hu ψt, neg_neg]
    _ = ∫ x, ψt x • U x (gen j k x) ∂((volume : Measure R3).restrict ballOpens) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hout2).symm
    _ = ∫ x, ψt x • w x ∂((volume : Measure R3).restrict ballOpens) := by
        apply integral_congr_ae
        filter_upwards [hw] with x hx
        rw [hx]
    _ = _ := (integral_smul_rotLp j k hjk t ψ w).symm

theorem integrable_testFunction_rot_smul (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ))
    (θ : ℝ) (u : Lp F 2 ((volume : Measure R3).restrict ballOpens)) :
    Integrable (fun x => ψ (rot j k hjk θ x) • u x) ((volume : Measure R3).restrict ballOpens) := by
  have hu : Integrable (⇑u) ((volume : Measure R3).restrict ballOpens) :=
    (MeasureTheory.Lp.memLp u).integrable one_le_two
  obtain ⟨C, hC⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  exact hu.bdd_smul C (ψ.continuous.comp (rot j k hjk θ).continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => hC _)

theorem pairL_rotLp_sub (j k : Fin 3) (hjk : j ≠ k) (ψ : 𝓓(ballOpens, ℝ))
    {u w : Lp F 2 ((volume : Measure R3).restrict ballOpens)} {U : R3 → R3 →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ballOpens (⇑u) U)
    (hw : ⇑w =ᵐ[(volume : Measure R3).restrict ballOpens] fun x => U x (gen j k x))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    pairL ψ (rotLp F j k hjk θ u) - pairL ψ u =
      ∫ t in (0:ℝ)..θ, pairL ψ (rotLp F j k hjk t w) := by
  simp_rw [pairL_apply]
  rw [integral_smul_rotLp]
  have h0 : (fun x => ψ x • u x) = fun x => ψ (rot j k hjk 0 x) • u x := by
    funext x; rw [rot_zero]
  rw [h0, ← integral_sub (integrable_testFunction_rot_smul j k hjk ψ _ u)
    (integrable_testFunction_rot_smul j k hjk ψ _ u)]
  simp_rw [← sub_smul, rot_zero, testFunction_rot_sub j k hjk ψ θ]
  rw [integral_integral_derivInt_swap j k hjk ψ hθ u]
  simp_rw [integral_derivInt_smul j k hjk ψ hu hw]

theorem rotLp_sub_eq_integral (j k : Fin 3) (hjk : j ≠ k)
    {u w : Lp F 2 ((volume : Measure R3).restrict ballOpens)} {U : R3 → R3 →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ballOpens (⇑u) U)
    (hw : ⇑w =ᵐ[(volume : Measure R3).restrict ballOpens] fun x => U x (gen j k x))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    rotLp F j k hjk θ u - u = ∫ t in (0:ℝ)..θ, rotLp F j k hjk t w := by
  rw [← sub_eq_zero]
  apply eq_zero_of_integral_testFunction_smul
  intro ψ
  rw [← pairL_apply, map_sub, map_sub, ← (pairL ψ).intervalIntegral_comp_comm
    ((continuous_rotLp j k hjk w).intervalIntegrable 0 θ), pairL_rotLp_sub j k hjk ψ hu hw hθ,
    sub_self]


/-- The rotational difference quotients converge in `L²(B; F)` to the derivative along the
generator. -/
theorem tendsto_slope_rotLp (j k : Fin 3) (hjk : j ≠ k)
    {u w : Lp F 2 ((volume : Measure R3).restrict ballOpens)} {U : R3 → R3 →L[ℝ] F}
    (hu : HasWeakFDerivOn volume ballOpens (⇑u) U)
    (hw : ⇑w =ᵐ[(volume : Measure R3).restrict ballOpens] fun x => U x (gen j k x)) :
    Tendsto (fun θ : ℝ => θ⁻¹ • (rotLp F j k hjk θ u - u)) (𝓝[>] 0) (𝓝 w) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.1
    (continuous_rotLp j k hjk w).continuousAt (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {θ} hθpos hθδ => ?_⟩
  have hθ : 0 < θ := hθpos
  have hcont := continuous_rotLp j k hjk w
  have heq : θ⁻¹ • (rotLp F j k hjk θ u - u) - w =
      θ⁻¹ • ∫ t in (0:ℝ)..θ, (rotLp F j k hjk t w - w) := by
    rw [rotLp_sub_eq_integral j k hjk hu hw hθ.le, intervalIntegral.integral_sub
      (hcont.intervalIntegrable 0 θ) intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ hθ.ne', one_smul]
  rw [dist_eq_norm, heq, norm_smul]
  have hb : ‖∫ t in (0:ℝ)..θ, (rotLp F j k hjk t w - w)‖ ≤ ε / 2 * |θ - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hθ.le] at ht
    have htd : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
      rw [Real.dist_eq, sub_zero, abs_of_pos hθ] at hθδ
      exact lt_of_le_of_lt ht.2 hθδ
    have := hδw htd
    rw [dist_eq_norm, rotLp_zero] at this
    exact this.le
  rw [sub_zero, abs_of_pos hθ] at hb
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hθ)]
  calc θ⁻¹ * ‖∫ t in (0:ℝ)..θ, (rotLp F j k hjk t w - w)‖ ≤ θ⁻¹ * (ε / 2 * θ) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε


/-! ### Rotation matrices and `L²` composition -/

theorem memLp_apply_gen (j k : Fin 3) (hjk : j ≠ k) {U : R3 → R3 →L[ℝ] F}
    (hU : MemLp U 2 ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x => U x (gen j k x)) 2 ((volume : Measure R3).restrict ballOpens) := by
  refine hU.of_le ?_ ?_
  · exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := R3) (F := F)).continuous.comp_aestronglyMeasurable₂
      hU.aestronglyMeasurable (continuous_gen_field j k).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    refine ((U x).le_opNorm _).trans ?_
    have h1 : ‖gen j k x‖ ≤ 1 := by
      refine (norm_gen_le j k hjk x).trans ?_
      have : x ∈ Metric.ball (0 : R3) 1 := hx
      rw [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    calc ‖U x‖ * ‖gen j k x‖ ≤ ‖U x‖ * 1 := by gcongr
      _ = ‖U x‖ := mul_one _

/-- The inverse rotation as a continuous linear map. -/
def rotInvCLM (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) : R3 →L[ℝ] R3 :=
  ((rot j k hjk θ).symm.toContinuousLinearEquiv : R3 →L[ℝ] R3)

/-- The projection onto the rotation plane. -/
def planeP (j k : Fin 3) : R3 →L[ℝ] R3 :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).smulRight (EuclideanSpace.single j (1:ℝ)) +
    (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).smulRight (EuclideanSpace.single k (1:ℝ))

/-- The generator as a continuous linear map. -/
def planeJ (j k : Fin 3) : R3 →L[ℝ] R3 :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).smulRight (EuclideanSpace.single k (1:ℝ)) -
    (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).smulRight (EuclideanSpace.single j (1:ℝ))

theorem rotInvCLM_eq (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ) :
    rotInvCLM j k hjk θ = ContinuousLinearMap.id ℝ R3 + (Real.cos θ - 1) • planeP j k -
      Real.sin θ • planeJ j k := by
  ext1 x
  rw [rotInvCLM, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    rot_symm, rot_apply_formula]
  simp only [Real.cos_neg, Real.sin_neg, planeP, planeJ, _root_.add_apply, _root_.sub_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply]
  rw [show (EuclideanSpace.proj j : R3 →L[ℝ] ℝ) x = x j from rfl,
    show (EuclideanSpace.proj k : R3 →L[ℝ] ℝ) x = x k from rfl, neg_smul, sub_eq_add_neg]
  abel

theorem rotFormula_zero (j k : Fin 3) :
    ContinuousLinearMap.id ℝ R3 + (Real.cos 0 - 1) • planeP j k - Real.sin 0 • planeJ j k =
      ContinuousLinearMap.id ℝ R3 := by
  ext1 x
  simp

theorem tendsto_rotInvCLM (j k : Fin 3) (hjk : j ≠ k) :
    Tendsto (rotInvCLM j k hjk) (𝓝 0) (𝓝 (ContinuousLinearMap.id ℝ R3)) := by
  have h : Continuous fun θ : ℝ => ContinuousLinearMap.id ℝ R3 + (Real.cos θ - 1) • planeP j k -
      Real.sin θ • planeJ j k := by fun_prop
  have := h.tendsto 0
  rw [rotFormula_zero] at this
  rw [show rotInvCLM j k hjk = _ from funext (rotInvCLM_eq j k hjk)]
  exact this

theorem tendsto_slope_rotInvCLM (j k : Fin 3) (hjk : j ≠ k) :
    Tendsto (fun θ : ℝ => θ⁻¹ • (rotInvCLM j k hjk θ - ContinuousLinearMap.id ℝ R3)) (𝓝[>] 0)
      (𝓝 (-planeJ j k)) := by
  have h : HasDerivAt (fun θ : ℝ => ContinuousLinearMap.id ℝ R3 + (Real.cos θ - 1) • planeP j k -
      Real.sin θ • planeJ j k) ((-Real.sin 0) • planeP j k - Real.cos 0 • planeJ j k) 0 := by
    have h1 := (((Real.hasDerivAt_cos 0).sub_const 1).smul_const (planeP j k)).const_add
      (ContinuousLinearMap.id ℝ R3)
    exact h1.sub ((Real.hasDerivAt_sin 0).smul_const (planeJ j k))
  have hd : (-Real.sin 0) • planeP j k - Real.cos 0 • planeJ j k = -planeJ j k := by
    ext1 x; simp
  have := h.tendsto_slope_zero_right
  rw [hd, rotFormula_zero] at this
  simp only [zero_add] at this
  simp only [rotInvCLM_eq j k hjk]
  exact this

theorem id_compLpL (f : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    (ContinuousLinearMap.id ℝ R3).compLpL 2 ((volume : Measure R3).restrict ballOpens) f = f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (ContinuousLinearMap.id ℝ R3) f]
    with x hx
  rw [hx, ContinuousLinearMap.id_apply]

theorem compLpL_sub_compLpL (L L' : R3 →L[ℝ] R3)
    (f : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    L.compLpL 2 ((volume : Measure R3).restrict ballOpens) f -
      L'.compLpL 2 ((volume : Measure R3).restrict ballOpens) f =
      (L - L').compLpL 2 ((volume : Measure R3).restrict ballOpens) f := by
  have h := ContinuousLinearMap.add_compLpL (p := 2)
    (μ := (volume : Measure R3).restrict ballOpens) (L - L') L'
  rw [sub_add_cancel] at h
  rw [h, _root_.add_apply, add_sub_cancel_right]

theorem norm_compLpL_apply_le (L : R3 →L[ℝ] R3)
    (f : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    ‖L.compLpL 2 ((volume : Measure R3).restrict ballOpens) f‖ ≤ ‖L‖ * ‖f‖ :=
  ((L.compLpL 2 _).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le L) (norm_nonneg _))

theorem tendsto_compLpL_apply {ι : Type*} {l : Filter ι} {A : ι → R3 →L[ℝ] R3}
    {D : ι → Lp R3 2 ((volume : Measure R3).restrict ballOpens)} {A0 : R3 →L[ℝ] R3}
    {X : Lp R3 2 ((volume : Measure R3).restrict ballOpens)}
    (hA : Tendsto A l (𝓝 A0)) (hD : Tendsto D l (𝓝 X)) :
    Tendsto (fun i => (A i).compLpL 2 ((volume : Measure R3).restrict ballOpens) (D i)) l
      (𝓝 (A0.compLpL 2 ((volume : Measure R3).restrict ballOpens) X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hA hD ⊢
  have hAn : Tendsto (fun i => ‖A i‖) l (𝓝 ‖A0‖) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.2 hA).norm
    exact this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (by simpa using (hAn.mul hD).add (hA.mul_const ‖X‖))
  have e : (A i).compLpL 2 ((volume : Measure R3).restrict ballOpens) (D i) -
      A0.compLpL 2 ((volume : Measure R3).restrict ballOpens) X =
      (A i).compLpL 2 ((volume : Measure R3).restrict ballOpens) (D i - X) +
      ((A i).compLpL 2 ((volume : Measure R3).restrict ballOpens) X -
        A0.compLpL 2 ((volume : Measure R3).restrict ballOpens) X) := by
    rw [map_sub]; abel
  rw [e, compLpL_sub_compLpL]
  exact (norm_add_le _ _).trans (add_le_add (norm_compLpL_apply_le _ _)
    (norm_compLpL_apply_le _ _))


/-! ### Assembly -/

theorem cauchySeq_of_tendsto_value_gradient {f : ℕ → W1p (volume : Measure R3) ballOpens 2}
    {a : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {b : Lp R3 2 ((volume : Measure R3).restrict ballOpens)}
    (ha : Tendsto (fun n => W1p.value (f n)) atTop (𝓝 a))
    (hb : Tendsto (fun n => W1p.gradient (f n)) atTop (𝓝 b)) : CauchySeq f := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N1, h1⟩ := Metric.cauchySeq_iff.1 ha.cauchySeq (ε / 2) (half_pos hε)
  obtain ⟨N2, h2⟩ := Metric.cauchySeq_iff.1 hb.cauchySeq (ε / 2) (half_pos hε)
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have e1 : W1p.value (f m - f n) = W1p.value (f m) - W1p.value (f n) := by
    simp only [← W1p.valueL_apply, map_sub]
  have e2 : W1p.gradient (f m - f n) = W1p.gradient (f m) - W1p.gradient (f n) := by
    simp only [← W1p.gradientL_apply, map_sub]
  rw [dist_eq_norm]
  calc ‖f m - f n‖ ≤ ‖W1p.value (f m - f n)‖ + ‖W1p.gradient (f m - f n)‖ :=
        W1p.norm_le_norm_value_add_norm_gradient _
    _ = dist (W1p.value (f m)) (W1p.value (f n)) +
        dist (W1p.gradient (f m)) (W1p.gradient (f n)) := by
        rw [e1, e2, dist_eq_norm, dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add (h1 m (le_of_max_le_left hm) n (le_of_max_le_left hn))
        (h2 m (le_of_max_le_right hm) n (le_of_max_le_right hn))
    _ = ε := add_halves ε

theorem smul_compLpL_apply (c : ℝ) (L : R3 →L[ℝ] R3)
    (f : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    (c • L).compLpL 2 ((volume : Measure R3).restrict ballOpens) f =
      c • L.compLpL 2 ((volume : Measure R3).restrict ballOpens) f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (c • L) f,
    ContinuousLinearMap.coeFn_compLpL (p := 2) L f,
    Lp.coeFn_smul c (L.compLpL 2 ((volume : Measure R3).restrict ballOpens) f)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, _root_.smul_apply]

theorem slope_alg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E →L[ℝ] E)
    (c : ℝ) (x y : E) : c • (A x - y) = A (c • (x - y)) + c • (A y - y) := by
  rw [map_smul, map_sub, ← smul_add, sub_add_sub_cancel]

theorem value_slope_rotate (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (v : W1p (volume : Measure R3) ballOpens 2) :
    W1p.value (θ⁻¹ • (rotate j k hjk θ v - v)) =
      θ⁻¹ • (rotLp ℝ j k hjk θ (W1p.value v) - W1p.value v) := by
  simp only [← W1p.valueL_apply, map_smul, map_sub]
  rw [W1p.valueL_apply, W1p.valueL_apply, rotate_apply, value_rotateFun]
  rfl

theorem gradient_slope_rotate (j k : Fin 3) (hjk : j ≠ k) (θ : ℝ)
    (v : W1p (volume : Measure R3) ballOpens 2) :
    W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) =
      (rotInvCLM j k hjk θ).compLpL 2 ((volume : Measure R3).restrict ballOpens)
        (θ⁻¹ • (rotLp R3 j k hjk θ (W1p.gradient v) - W1p.gradient v)) +
      (θ⁻¹ • (rotInvCLM j k hjk θ - ContinuousLinearMap.id ℝ R3)).compLpL 2
        ((volume : Measure R3).restrict ballOpens) (W1p.gradient v) := by
  have h1 : W1p.gradient (θ⁻¹ • (rotate j k hjk θ v - v)) =
      θ⁻¹ • (rotGradL j k hjk θ (W1p.gradient v) - W1p.gradient v) := by
    rw [← gradient_rotateFun, ← rotate_apply, W1p.gradient_smul]
    simp only [← W1p.gradientL_apply, map_sub]
  have h2 : rotGradL j k hjk θ (W1p.gradient v) =
      (rotInvCLM j k hjk θ).compLpL 2 ((volume : Measure R3).restrict ballOpens)
        (rotLp R3 j k hjk θ (W1p.gradient v)) := rfl
  have h3 : (θ⁻¹ • (rotInvCLM j k hjk θ - ContinuousLinearMap.id ℝ R3)).compLpL 2
      ((volume : Measure R3).restrict ballOpens) (W1p.gradient v) =
      θ⁻¹ • ((rotInvCLM j k hjk θ).compLpL 2 ((volume : Measure R3).restrict ballOpens)
        (W1p.gradient v) - W1p.gradient v) := by
    rw [smul_compLpL_apply, ← compLpL_sub_compLpL, id_compLpL]
  rw [h1, h2, h3]
  exact slope_alg _ _ _ _

/-- If `v ∈ H¹₀(B)` is the first-order part of an element of `H²(B)`, then the rotational
derivative `⟪gen j k x, ∇v x⟫` is (the value of) an element of `H¹₀(B)`. -/
theorem exists_rotational_mem_w1p0 {v : W1p (volume : Measure R3) ballOpens 2}
    (hv0 : v ∈ w1p0Submodule (volume : Measure R3) ballOpens 2)
    (V : Wkp (volume : Measure R3) ballOpens 2 2) (hV : Wkp.lowerOrder 1 V = v)
    (j k : Fin 3) (hjk : j ≠ k) :
    ∃ z : W1p (volume : Measure R3) ballOpens 2,
      z ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 ∧
      ⇑(W1p.value z) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ⟪gen j k x, W1p.gradient v x⟫_ℝ := by
  -- the value part
  have hvW : HasWeakFDerivOn volume ballOpens (⇑(W1p.value v))
      (fun x => innerSL ℝ (W1p.gradient v x)) := W1p.hasWeakFDerivOn v
  have hUv : MemLp (fun x => innerSL ℝ (W1p.gradient v x)) 2
      ((volume : Measure R3).restrict ballOpens) :=
    (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ).comp_memLp' (MeasureTheory.Lp.memLp _)
  have hXv := memLp_apply_gen j k hjk hUv
  have hval := tendsto_slope_rotLp j k hjk hvW hXv.coeFn_toLp
  -- the gradient part
  have hG : HasWeakFDerivOn volume ballOpens (⇑(W1p.gradient v))
      (fun x => (Wkp.iteratedGradient 1 V x : R3 →L[ℝ] R3)) := by
    have h := Wkp.hasWeakFDerivOn_iteratedGradient 0 V
    rw [Wkp.iteratedGradient_zero, hV] at h
    exact h
  have hUG : MemLp (fun x => (Wkp.iteratedGradient 1 V x : R3 →L[ℝ] R3)) 2
      ((volume : Measure R3).restrict ballOpens) := MeasureTheory.Lp.memLp _
  have hXG := memLp_apply_gen j k hjk hUG
  have hgradlim := tendsto_slope_rotLp j k hjk hG hXG.coeFn_toLp
  have hgr := (tendsto_compLpL_apply
      ((tendsto_rotInvCLM j k hjk).mono_left nhdsWithin_le_nhds) hgradlim).add
    (tendsto_compLpL_apply (tendsto_slope_rotInvCLM j k hjk)
      (tendsto_const_nhds (x := W1p.gradient v)))
  -- the sequence of difference quotients
  have hθs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  have hfv : Tendsto (fun n : ℕ => W1p.value ((1 / ((n : ℝ) + 1))⁻¹ •
      (rotate j k hjk (1 / ((n : ℝ) + 1)) v - v))) atTop (𝓝 (hXv.toLp _)) := by
    simp only [value_slope_rotate]
    exact hval.comp hθs
  have hfg : Tendsto (fun n : ℕ => W1p.gradient ((1 / ((n : ℝ) + 1))⁻¹ •
      (rotate j k hjk (1 / ((n : ℝ) + 1)) v - v))) atTop
      (𝓝 ((ContinuousLinearMap.id ℝ R3).compLpL 2 ((volume : Measure R3).restrict ballOpens)
          (hXG.toLp _) + (-planeJ j k).compLpL 2 ((volume : Measure R3).restrict ballOpens)
          (W1p.gradient v))) := by
    simp only [gradient_slope_rotate]
    exact hgr.comp hθs
  have hz := cauchySeq_tendsto_of_complete (cauchySeq_of_tendsto_value_gradient hfv hfg)
  refine ⟨hz.choose, ?_, ?_⟩
  · refine (w1p0Submodule (volume : Measure R3) ballOpens 2).isClosed.mem_of_tendsto
      hz.choose_spec (Eventually.of_forall fun n => ?_)
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (rotate_mem_w1p0Submodule j k hjk _ hv0) hv0)
  · have hzv : W1p.value hz.choose = hXv.toLp _ :=
      tendsto_nhds_unique ((W1p.valueL.continuous.tendsto hz.choose).comp hz.choose_spec) hfv
    rw [hzv]
    filter_upwards [hXv.coeFn_toLp] with x hx
    rw [hx, innerSL_apply_apply, real_inner_comm]

end OAI.AnisotropicCalderon.Rotation
