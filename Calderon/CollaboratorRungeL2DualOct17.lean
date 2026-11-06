import Calderon.CollaboratorRungeL2LocalOct17

/-! The duality argument for the `L²` Runge approximation `l2_runge`
(Lassas–Liimatainen–Salo Prop. A.6). -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.RungeAux
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine

/-- The conclusion of interior smoothness of weak solutions, as a hypothesis. -/
def SmoothOfWeak (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ {O : Set R3}, IsOpen O → ∀ {w : R3 → ℝ},
    (∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ W : W1p (volume : Measure R3) (ballO x ρ) 2,
      ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w ∧
      ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ x in ball x ρ,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient W x) = 0) →
    ∃ w' : R3 → ℝ, ContDiffOn ℝ ∞ w' O ∧ w' =ᵐ[(volume : Measure R3).restrict O] w ∧
      ∀ x ∈ O, divCoeffGrad A w' x = 0

/-- Step 2: the dual solution vanishes on the source set. -/
theorem ae_zero_on_sources {c : R3} {R : ℝ} {W : Opens R3} (hW : (W : Set R3) ⊆ ball c R)
    (w : W1p (volume : Measure R3) (ballO c R) 2)
    (h : ∀ f : 𝓓(W, ℝ), ∫ x in ball c R, (f : R3 → ℝ) x * W1p.value w x = 0) :
    ∀ᵐ x ∂(volume : Measure R3).restrict W, W1p.value w x = 0 := by
  have : IsFiniteMeasure ((volume : Measure R3).restrict ((ballO c R : Opens R3) : Set R3)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (W1p.value w : R3 → ℝ) (ball c R) :=
    (Lp.memLp (W1p.value w)).integrable one_le_two
  have hloc : LocallyIntegrableOn (W1p.value w : R3 → ℝ) (W : Set R3) :=
    (hint.mono_set hW).locallyIntegrableOn
  have key := W.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hloc
    (fun g hg hgc hgs => by
      have h0 := h ⟨g, hg, hgc, hgs⟩
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hW (hgs h'))
        simp [this])] at h0
      simpa [smul_eq_mul] using h0)
  rw [ae_restrict_iff' W.isOpen.measurableSet]
  exact key

/-- Step 3: the dual solution is a local weak solution off `closure U`. -/
theorem local_weak_off {c : R3} {R : ℝ} {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {U : Set R3}
    (hUM : U ⊆ ball c R) (h : R3 → ℝ)
    (w : W1p (volume : Measure R3) (ballO c R) 2)
    (hdual : ∀ φ : W1p (volume : Measure R3) (ballO c R) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
      ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in U, h x * W1p.value φ x) :
    ∀ x ∈ ball c R \ closure U, ∃ ρ > 0, ball x ρ ⊆ ball c R \ closure U ∧
      ∃ W : W1p (volume : Measure R3) (ballO x ρ) 2,
      ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] ⇑(W1p.value w) ∧
      ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ x in ball x ρ,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient W x) = 0 := by
  intro x hx
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpen_ball.sdiff isClosed_closure) x hx
  have hB : ballO x ρ ≤ ballO c R := fun y hy => (hball hy).1
  refine ⟨ρ, hρ, hball, W1p.restrictL hB w, W1p.value_restrictL_ae hB w, fun φ => ?_⟩
  have e1 := integral_mono_test hB A w φ
  have e2 := hdual _ (W1p.ofTestFunctionₗ_mem_w1p0Submodule (TestFunction.monoCLM ℝ φ))
  have e3 := integral_mono_test_value hB hUM h φ
  have e4 : ∫ y in U, h y * (φ : R3 → ℝ) y = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hyn : y ∉ ((ballO x ρ : Opens R3) : Set R3) := fun hy' =>
      (hball hy').2 (subset_closure hy)
    rw [eq_zero_of_notMem φ hyn, mul_zero]
  exact e1.symm.trans (e2.trans (e3.trans e4))

/-- Step 3, unique continuation: a local weak solution on a connected open set vanishing
on a nonempty open subset vanishes. -/
theorem ae_zero_of_ucp (hUCP : UniqueContinuation) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) (hreg : SmoothOfWeak A) {O : Set R3}
    (hO : IsOpen O) (hconn : IsConnected O) {V : Set R3} (hV : IsOpen V) (hVne : V.Nonempty)
    (hVO : V ⊆ O) {w : R3 → ℝ}
    (hloc : ∀ x ∈ O, ∃ ρ > 0, ball x ρ ⊆ O ∧ ∃ W : W1p (volume : Measure R3) (ballO x ρ) 2,
      ⇑(W1p.value W) =ᵐ[(volume : Measure R3).restrict (ball x ρ)] w ∧
      ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ x in ball x ρ,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient W x) = 0)
    (hzero : ∀ᵐ x ∂(volume : Measure R3).restrict V, w x = 0) :
    ∀ᵐ x ∂(volume : Measure R3).restrict O, w x = 0 := by
  obtain ⟨w', hw's, hw'ae, hw'div⟩ := hreg hO hloc
  have hV0 : Set.EqOn w' (fun _ => (0 : ℝ)) V := by
    refine Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) ?_ hV (hw's.continuousOn.mono hVO) continuousOn_const
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVO hw'ae, hzero] with x h1 h2
    rw [h1, h2]
  have hO0 := hUCP O hO hconn A hA.contDiffOn (fun x _ => hpos x) w' hw's hw'div V hV hVne hVO
    hV0
  filter_upwards [hw'ae, ae_restrict_mem hO.measurableSet] with x h1 h2
  rw [← h1, hO0 x h2]

/-- Step 5: testing the dual equation with `χ u0`. -/
theorem final_identity {U U' : Set R3} (hU : IsOpen U) (hU' : IsOpen U') (hUU' : closure U ⊆ U')
    (hcomp : IsCompact (closure U)) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hpos : ∀ x, (A x).PosDef) (h : R3 → ℝ) (F : R3 → ℝ)
    (hF : ∀ g : R3 → ℝ, ∫ x in U', F x * g x = ∫ x in U, h x * g x)
    (wU : W1p (volume : Measure R3) ⟨U', hU'⟩ 2)
    (hwU0 : wU ∈ w1p0Submodule (volume : Measure R3) ⟨U', hU'⟩ 2)
    (hgrad : ∀ᵐ x ∂(volume : Measure R3).restrict U', x ∉ closure U → W1p.gradient wU x = 0)
    (hdualU : ∀ φ : W1p (volume : Measure R3) ⟨U', hU'⟩ 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ⟨U', hU'⟩ 2 →
      ∫ x in U', matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient wU x) =
        ∫ x in U', F x * W1p.value φ x)
    (u0 : W1p (volume : Measure R3) ⟨U', hU'⟩ 2)
    (hu0 : ∀ φ : W1p (volume : Measure R3) ⟨U', hU'⟩ 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ⟨U', hU'⟩ 2 →
      ∫ x in U', matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient u0 x) = 0) :
    ∫ x in U, h x * W1p.value u0 x = 0 := by
  obtain ⟨χ, M, hχ, -, hχone, hχcpt, hχts, hM0, hχM, hgradM⟩ :=
    hcomp.exists_contDiff_cutoff_with_bounds hU' hUU'
  have hχS : ∀ x ∈ closure U, χ x = 1 ∧ ∇ χ x = 0 := fun x hx => by
    have hev : χ =ᶠ[nhds x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hχone hx)) fun y hy => hy
    refine ⟨hev.eq_of_nhds, ?_⟩
    rw [_root_.gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]
  have hΦ0 := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hχ hM0
    (fun x _ => hχM x) (fun x _ => hgradM x) hχcpt hχts u0
  have e1 := hdualU _ hΦ0
  have e2 := hF (W1p.value (W1p.contDiffSMul χ hχ hM0 (fun x _ => hχM x) (fun x _ => hgradM x)
    u0))
  have hUsub : U ⊆ U' := subset_closure.trans hUU'
  have e3 : ∫ x in U, h x * W1p.value (W1p.contDiffSMul χ hχ hM0 (fun x _ => hχM x)
      (fun x _ => hgradM x) u0) x = ∫ x in U, h x * W1p.value u0 x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUsub
      (W1p.value_contDiffSMul_ae hχ hM0 (fun x _ => hχM x) (fun x _ => hgradM x) u0),
      ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hx, (hχS x (subset_closure hxU)).1, one_smul]
  have e4 : ∫ x in U', matrixBilinearForm (A x) (W1p.gradient (W1p.contDiffSMul χ hχ hM0
      (fun x _ => hχM x) (fun x _ => hgradM x) u0) x) (W1p.gradient wU x) =
      ∫ x in U', matrixBilinearForm (A x) (W1p.gradient wU x) (W1p.gradient u0 x) := by
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_contDiffSMul_ae hχ hM0 (fun x _ => hχM x) (fun x _ => hgradM x)
      u0, hgrad] with x hx hxg
    rw [hx]
    by_cases hxU : x ∈ closure U
    · rw [(hχS x hxU).1, (hχS x hxU).2, one_smul, smul_zero, add_zero, mbf_symm (hpos x)]
    · rw [hxg hxU]
      simp
  have e5 := hu0 wU hwU0
  rw [← e3, ← e2, ← e1, e4, e5]

/-- **The duality argument.** A function `h ∈ L²(U)` orthogonal to all `K f` is orthogonal
to every local solution `u0`. -/
theorem orth_core (hUCP : UniqueContinuation) (c : R3) {R : ℝ} (hR : 0 < R)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef)
    (hreg : SmoothOfWeak A)
    {W : Opens R3} (hWne : (W : Set R3).Nonempty) (hW : (W : Set R3) ⊆ ball c R)
    (K : 𝓓(W, ℝ) → W1p (volume : Measure R3) (ballO c R) 2)
    (hK0 : ∀ f, K f ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2)
    (hK : ∀ f (φ : W1p (volume : Measure R3) (ballO c R) 2),
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
      ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient (K f) x) =
        ∫ x in ball c R, (f : R3 → ℝ) x * W1p.value φ x)
    {U U' : Set R3} (hU : IsOpen U) (hU' : IsOpen U') (hUU' : closure U ⊆ U')
    (hU'M : U' ⊆ ball c R) (hWU : Disjoint (W : Set R3) (closure U))
    (hconn : IsConnected (ball c R \ closure U))
    (u0 : W1p (volume : Measure R3) ⟨U', hU'⟩ 2)
    (hu0 : ∀ φ : 𝓓((⟨U', hU'⟩ : Opens R3), ℝ), ∫ x in U',
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u0 x) = 0)
    (h : Lp ℝ 2 ((volume : Measure R3).restrict U))
    (horth : ∀ f, ∫ x in U, h x * W1p.value (K f) x = 0) :
    ∫ x in U, h x * W1p.value u0 x = 0 := by
  have hAc : Continuous A := hA.continuous
  have hUM : U ⊆ ball c R := subset_closure.trans (hUU'.trans hU'M)
  obtain ⟨F, hF⟩ := exists_extL hU.measurableSet hUM h
  obtain ⟨w, hw0, hw⟩ := exists_weak c hR hAc hpos F
  have hdual : ∀ φ : W1p (volume : Measure R3) (ballO c R) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
      ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in U, h x * W1p.value φ x := fun φ hφ => (hw φ hφ).trans (hF _)
  have hD1 : ∀ f : 𝓓(W, ℝ), ∫ x in ball c R, (f : R3 → ℝ) x * W1p.value w x = 0 := by
    intro f
    rw [← hK f w hw0]
    have hs : ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient w x)
        (W1p.gradient (K f) x) = ∫ x in ball c R, matrixBilinearForm (A x)
        (W1p.gradient (K f) x) (W1p.gradient w x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mbf_symm (hpos x) _ _)
    rw [hs]
    exact (hdual _ (hK0 f)).trans (horth f)
  have hD2 := ae_zero_on_sources hW w hD1
  have hWO : (W : Set R3) ⊆ ball c R \ closure U := fun x hx =>
    ⟨hW hx, Set.disjoint_left.1 hWU hx⟩
  have hO : IsOpen (ball c R \ closure U) := isOpen_ball.sdiff isClosed_closure
  have hD4 := ae_zero_of_ucp hUCP hA hpos hreg hO hconn W.isOpen hWne hWO
    (local_weak_off hUM h w hdual) hD2
  have hΩ : (⟨U', hU'⟩ : Opens R3) ≤ ballO c R := hU'M
  have hcomp : IsCompact (closure U) := (isBounded_ball.subset hUM).isCompact_closure
  have hD4' := (ae_restrict_iff' hO.measurableSet).1 hD4
  have hval : ∀ᵐ x ∂(volume : Measure R3).restrict U', x ∉ closure U →
      W1p.value (W1p.restrictL hΩ w) x = 0 := by
    filter_upwards [W1p.value_restrictL_ae hΩ w, ae_restrict_mem hU'.measurableSet,
      ae_restrict_of_ae hD4'] with x h1 h2 h3 hx
    rw [h1, h3 ⟨hU'M h2, hx⟩]
  have hwU0 := W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hcomp hUU' hval
  have hgrad : ∀ᵐ x ∂(volume : Measure R3).restrict U', x ∉ closure U →
      W1p.gradient (W1p.restrictL hΩ w) x = 0 := by
    let V : Opens R3 := ⟨U' \ closure U, hU'.sdiff isClosed_closure⟩
    have hVmeas : MeasurableSet (V : Set R3) := V.isOpen.measurableSet
    have hvalV : ∀ᵐ x ∂(volume : Measure R3).restrict (V : Set R3),
        W1p.value (W1p.restrictL hΩ w) x = 0 := by
      rw [ae_restrict_iff' hVmeas]
      filter_upwards [(ae_restrict_iff' hU'.measurableSet).1 hval] with x hx hxV
      exact hx hxV.1 hxV.2
    have hgradV := (ae_restrict_iff' hVmeas).1
      (W1p.gradient_ae_eq_zero_of_value_ae_eq_zero (V := V) Set.sdiff_subset hvalV)
    rw [ae_restrict_iff' hU'.measurableSet]
    filter_upwards [hgradV] with x hx hxO hxK
    exact hx ⟨hxO, hxK⟩
  obtain ⟨C, hC⟩ := exists_norm_mvA_le hAc c R
  have hC' : ∀ x ∈ ((⟨U', hU'⟩ : Opens R3) : Set R3), ‖mvA (A x)‖ ≤ C :=
    fun x hx => hC x (hU'M hx)
  obtain ⟨FU, hFU⟩ := exists_extL hU.measurableSet (subset_closure.trans hUU') h
  have hdualU := eq_of_test hAc hC' (G := W1p.gradient (W1p.restrictL hΩ w)) (F := FU)
    (fun ψ => (integral_mono_test hΩ A w ψ).symm.trans ((hdual _
      (W1p.ofTestFunctionₗ_mem_w1p0Submodule _)).trans
      ((integral_mono_test_value hΩ hUM h ψ).trans (hFU _).symm)))
  have hzero : ∀ g : R3 → ℝ, ∫ x in U',
      (0 : Lp ℝ 2 ((volume : Measure R3).restrict U')) x * g x = 0 := fun g => by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict U')] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  have hu0' := eq_of_test hAc hC' (G := W1p.gradient u0)
    (F := (0 : Lp ℝ 2 ((volume : Measure R3).restrict U')))
    (fun ψ => (hu0 ψ).trans (hzero _).symm)
  exact final_identity hU hU' hUU' hcomp hpos h FU hFU (W1p.restrictL hΩ w) hwU0 hgrad
    hdualU u0 (fun φ hφ => (hu0' φ hφ).trans (hzero _))

/-! ### Hilbert space duality -/

theorem approx_of_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {D : Type*} [AddCommGroup D] [Module ℝ D] (T : D → H)
    (hT : ∀ (a : ℝ) (f g : D), T (a • f + g) = a • T f + T g) (v : H)
    (horth : ∀ h : H, (∀ f, ⟪T f, h⟫_ℝ = 0) → ⟪v, h⟫_ℝ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, ‖T f - v‖ < ε := by
  have h0 : T 0 = 0 := by
    have := hT 1 0 0
    simp only [smul_zero, add_zero, one_smul] at this
    simpa using this
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range T)
  have hS : ∀ y ∈ S, ∃ f, T f = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, h0⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨(1 : ℝ) • f + g, by rw [hT, one_smul]⟩
    | smul a x _ hx =>
      obtain ⟨f, rfl⟩ := hx
      exact ⟨a • f + 0, by rw [hT, h0, add_zero]⟩
  have hv : v ∈ S.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro h hh
    rw [real_inner_comm]
    refine horth h fun f => ?_
    exact (Submodule.mem_orthogonal S h).1 hh _ (Submodule.subset_span ⟨f, rfl⟩)
  obtain ⟨y, hyS, hy⟩ := Metric.mem_closure_iff.1 hv ε hε
  obtain ⟨f, rfl⟩ := hS y hyS
  exact ⟨f, by rw [← dist_eq_norm, dist_comm]; exact hy⟩

/-! ### Linearity of the solution map -/

theorem integrable_test_mul {c : R3} {R : ℝ} {W : Opens R3} (f : 𝓓(W, ℝ))
    (φ : W1p (volume : Measure R3) (ballO c R) 2) :
    Integrable (fun x => (f : R3 → ℝ) x * W1p.value φ x)
      ((volume : Measure R3).restrict (ball c R)) := by
  have : IsFiniteMeasure ((volume : Measure R3).restrict ((ballO c R : Opens R3) : Set R3)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (W1p.value φ : R3 → ℝ)
      ((volume : Measure R3).restrict ((ballO c R : Opens R3) : Set R3)) :=
    (Lp.memLp (W1p.value φ)).integrable one_le_two
  exact hint.mul_of_top_right f.memLp_top

theorem K_add_smul (c : R3) {R : ℝ} (hR : 0 < R)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) (hpos : ∀ x, (A x).PosDef)
    {W : Opens R3}
    (K : 𝓓(W, ℝ) → W1p (volume : Measure R3) (ballO c R) 2)
    (hK0 : ∀ f, K f ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2)
    (hK : ∀ f (φ : W1p (volume : Measure R3) (ballO c R) 2),
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
      ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient (K f) x) =
        ∫ x in ball c R, (f : R3 → ℝ) x * W1p.value φ x)
    (a : ℝ) (f g : 𝓓(W, ℝ)) : K (a • f + g) = a • K f + K g := by
  obtain ⟨C, hC⟩ := exists_norm_mvA_le hA c R
  have hC' : ∀ x ∈ ((ballO c R : Opens R3) : Set R3), ‖mvA (A x)‖ ≤ C := hC
  refine eq_of_weak c hR hA hpos (hK0 _) (add_mem (Submodule.smul_mem _ a (hK0 f)) (hK0 g))
    fun φ hφ => ?_
  rw [hK _ φ hφ]
  have e1 : ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x)
      (W1p.gradient (a • K f + K g) x) = ∫ x in ball c R,
        (a * matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient (K f) x) +
          matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient (K g) x)) := by
    refine integral_congr_ae ?_
    rw [w1_gradient_add, w1_gradient_smul]
    filter_upwards [Lp.coeFn_add (a • W1p.gradient (K f)) (W1p.gradient (K g)),
      Lp.coeFn_smul a (W1p.gradient (K f))] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, map_add, map_smul, smul_eq_mul]
  have e2 : ∫ x in ball c R, ((a • f + g : 𝓓(W, ℝ)) : R3 → ℝ) x * W1p.value φ x =
      ∫ x in ball c R, (a * ((f : R3 → ℝ) x * W1p.value φ x) +
        (g : R3 → ℝ) x * W1p.value φ x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have i1 : Integrable (fun x => matrixBilinearForm (A x) (W1p.gradient φ x)
      (W1p.gradient (K f) x)) ((volume : Measure R3).restrict (ball c R)) :=
    integrable_mbf hA hC' _ _
  have i2 : Integrable (fun x => matrixBilinearForm (A x) (W1p.gradient φ x)
      (W1p.gradient (K g) x)) ((volume : Measure R3).restrict (ball c R)) :=
    integrable_mbf hA hC' _ _
  rw [e1, e2, integral_add (i1.const_mul a) i2,
    integral_add ((integrable_test_mul f φ).const_mul a) (integrable_test_mul g φ),
    integral_const_mul, integral_const_mul, hK f φ hφ, hK g φ hφ]

end OAI.AnisotropicCalderon.Regularity.RungeAux
