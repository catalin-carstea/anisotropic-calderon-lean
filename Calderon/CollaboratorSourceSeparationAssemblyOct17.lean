import Calderon.CollaboratorSourceJetWeakEstimatesOct17
import Calderon.CollaboratorLocalSobolevRawTwoJetBoundOct17
import Calderon.CollaboratorLocalJetsOct17

/-! Task 09 assembly: source separation for the radius-two source problem, from weak unique
continuation.

Route: `L²` Runge approximation (`l2_runge`) on one or two small balls, with sources in a small
ball `W'` inside the fixed source ball avoiding the target points, of a compactly supported smooth
function solving the equation near the targets; the interior estimate and the local Sobolev jet
bound turn the `L²` error into an error of the value and the gradient at the target points.
Values are separated with a bump function; gradients form a (closed, finite-dimensional) linear
subspace which is dense by approximation of local solutions with prescribed 2-jets. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise Distributions Gradient
  Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.Literature.SepAux
open EnergyBridge DirichletFamily MetricVolume TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine


/-- `‖x‖` behind a non-projection head (see `nrmsub`). -/
def nrm {E : Type*} [SeminormedAddCommGroup E] (x : E) : ℝ := ‖x‖

theorem norm_eq_nrm {E : Type*} [SeminormedAddCommGroup E] (x : E) : ‖x‖ = nrm x := rfl

theorem divCoeffGrad_congr {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {f h : R3 → ℝ} {x : R3}
    (hfh : f =ᶠ[𝓝 x] h) : divCoeffGrad A f x = divCoeffGrad A h x := by
  unfold divCoeffGrad
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [hfh.fderiv (𝕜 := ℝ)] with z hz
  rw [hz]

theorem divCoeffGrad_const (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (c : ℝ) (x : R3) :
    divCoeffGrad A (fun _ => c) x = 0 := by
  simp [divCoeffGrad]

/-- A compactly supported smooth function solving the equation classically on an open set `O`
gives a weak solution on `O`. -/
theorem weak_testFn {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (O : Opens R3)
    (ψ : 𝓓((⊤ : Opens R3), ℝ)) (hψ : ∀ x ∈ (O : Set R3), divCoeffGrad A ψ x = 0)
    (φ : 𝓓(O, ℝ)) :
    ∫ x in (O : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x)
      (W1p.gradient (W1p.restrictL (le_top : O ≤ ⊤)
        (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) x) = 0 := by
  have h1 : ∫ x in (O : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x)
      (W1p.gradient (W1p.restrictL (le_top : O ≤ ⊤)
        (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) x) =
      ∫ x in (O : Set R3), matrixBilinearForm (A x) (∇ (φ : R3 → ℝ) x) (∇ (ψ : R3 → ℝ) x) := by
    refine integral_congr_ae ?_
    have h2 := ae_restrict_of_ae_restrict_of_subset (Set.subset_univ (O : Set R3))
      (gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ⊤) 2 ψ)
    filter_upwards [W1p.gradient_restrictL_ae (le_top : O ≤ ⊤)
      (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ), h2] with x hx1 hx2
    rw [hx1, W1p.gradient_ofTestFunctionₗ, hx2]
  rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [RungeAux.gradient_eq_zero_of_notMem φ hx]),
    IS.integral_mbf_eq hA ψ.contDiff φ.contDiff φ.hasCompactSupport]
  have : ∀ z, (φ : R3 → ℝ) z * divCoeffGrad A ψ z = 0 := fun z => by
    by_cases hz : z ∈ (O : Set R3)
    · rw [hψ z hz, mul_zero]
    · rw [RungeAux.eq_zero_of_notMem φ hz, zero_mul]
  simp [this]

/-- The local Sobolev jet bound, value and gradient components, on `ballO p r`. -/
theorem jet_bound_ballO (p : R3) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Wkp (volume : Measure R3) (ballO p r) 2 5) (uSmooth : R3 → ℝ),
      ContDiffOn ℝ ∞ uSmooth (ball p r) →
      (⇑(Wkp.value 5 u) =ᵐ[(volume : Measure R3).restrict (ball p r)] uSmooth) →
      |uSmooth p| ≤ C * nrm u ∧ ‖fderiv ℝ uSmooth p‖ ≤ C * nrm u := by
  obtain ⟨C, hC, hj⟩ := localSobolevRawTwoJetBound p r hr
  refine ⟨C, hC, fun u uS hs hae => ?_⟩
  have h := hj u uS hs hae
  erw [norm_eq_nrm u] at h
  have h' := norm_prod_le_iff.1 h
  refine ⟨?_, (norm_prod_le_iff.1 h'.2).1⟩
  have h0 := h'.1
  rwa [Real.norm_eq_abs] at h0

/-- **Pointwise jet error from `L²` error.** On a ball `ball p r₂` where the source vanishes and
a compactly supported smooth `ψ` solves the equation, the `L²(ball p r₂)` distance between the
source solution and `ψ` controls the value and gradient errors at `p`. -/
theorem jet_bound (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ)
    (hresp : IsRadiusTwoSmoothSourceResponse g hg response)
    (p : R3) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    (hsub : closedBall p r₂ ⊆ ball (0 : R3) 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓓(fixedExteriorSourceOpens, ℝ)) (ψ : 𝓓((⊤ : Opens R3), ℝ)),
      (∀ x ∈ ball p r₂, (f : R3 → ℝ) x = 0) →
      (∀ x ∈ ball p r₂, divCoeffGrad (principalCoefficient g) ψ x = 0) →
      ∀ δ : ℝ, 0 < δ →
      ∫ x in ball p r₂, (W1p.value (Kresp g hg f) x - (ψ : R3 → ℝ) x) ^ 2 < δ ^ 2 →
      |response f p - ψ p| ≤ C * δ ∧
        ‖fderiv ℝ (response f) p - fderiv ℝ (ψ : R3 → ℝ) p‖ ≤ C * δ := by
  have hA := contDiff_principalCoefficient g hg
  have hpos := principalCoefficient_posDef g hg
  obtain ⟨C, hC, hest⟩ := exists_weak_solution_rawJet_bound p hr₁ hr hA hpos
  refine ⟨C, hC, fun f ψ hf0 hψ δ hδ hint => ?_⟩
  have hle1 : ballO p r₂ ≤ ballO 0 2 := fun x hx => hsub (ball_subset_closedBall hx)
  have hleT : ballO p r₂ ≤ ⊤ := le_top
  have hKz := radiusTwoSourceSolution_restrict_weak_zero_of_source_zero
    g hg (ballO p r₂) hle1 f hf0
  have hΨz := weak_testFn hA (ballO p r₂) ψ hψ
  have hw := sub_weak_zero p r₂ hA.continuous hKz hΨz
  have hval : ⇑(W1p.value (W1p.restrictL hle1 (Kresp g hg f) -
        W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)))
      =ᵐ[(volume : Measure R3).restrict (ball p r₂)]
      fun x => W1p.value (Kresp g hg f) x - (ψ : R3 → ℝ) x := by
    have : W1p.value (W1p.restrictL hle1 (Kresp g hg f) -
          W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) =
        W1p.value (W1p.restrictL hle1 (Kresp g hg f)) -
          W1p.value (W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) := by
      simp only [← W1p.valueL_apply, map_sub]
    rw [this]
    have h4 := ae_restrict_of_ae_restrict_of_subset (Set.subset_univ (ball p r₂))
      (testFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ⊤) 2 ψ)
    filter_upwards [Lp.coeFn_sub (W1p.value (W1p.restrictL hle1 (Kresp g hg f)))
        (W1p.value (W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ))),
      W1p.value_restrictL_ae hle1 (Kresp g hg f),
      W1p.value_restrictL_ae hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ), h4]
      with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, W1p.value_ofTestFunctionₗ, h4]
  have hnorm : ‖W1p.value (W1p.restrictL hle1 (Kresp g hg f) -
      W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ))‖ < δ :=
    norm_lt_of_ae_integral_sq_lt (ballO p r₂) _ _ hval hδ.le hint
  have hpr : ball p r₁ ⊆ ball (0 : R3) 2 := fun x hx =>
    hsub (ball_subset_closedBall (ball_subset_ball hr.le hx))
  have hrs : ContDiffOn ℝ ∞ (fun x => response f x - (ψ : R3 → ℝ) x) (ball p r₁) :=
    ((hresp f).1.mono hpr).sub ψ.contDiff.contDiffOn
  have hKF := ae_restrict_of_ae_restrict_of_subset hpr (hresp f).2.2.1
  have hae : ⇑(W1p.value (W1p.restrictL hle1 (Kresp g hg f) -
        W1p.restrictL hleT (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)))
      =ᵐ[(volume : Measure R3).restrict (ball p r₁)]
      fun x => response f x - (ψ : R3 → ℝ) x := by
    have hsmall := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hr.le) hval
    filter_upwards [hsmall, hKF] with x h1 h2
    rw [h1, h2]
    all_goals rfl
  have hraw := hest _ hw _ hrs hae
  have hsmall : ‖(((response f p - ψ p),
      (fderiv ℝ (fun x => response f x - (ψ : R3 → ℝ) x) p,
        fderiv ℝ (fderiv ℝ (fun x => response f x - (ψ : R3 → ℝ) x)) p)) :
      RadiusTwoRawTwoJet)‖ ≤ C * δ :=
    hraw.trans (mul_le_mul_of_nonneg_left hnorm.le hC)
  have hparts := norm_prod_le_iff.1 hsmall
  have h0 := hparts.1
  rw [Real.norm_eq_abs] at h0
  have hd1 : DifferentiableAt ℝ (response f) p :=
    ((hresp f).1.contDiffAt (isOpen_ball.mem_nhds
      (hsub (mem_closedBall_self (hr₁.trans hr).le)))).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (ψ : R3 → ℝ) p := (ψ.contDiff.differentiable (by simp)) p
  have h1 := (norm_prod_le_iff.1 hparts.2).1
  change ‖fderiv ℝ (response f - (ψ : R3 → ℝ)) p‖ ≤ C * δ at h1
  rw [fderiv_sub hd1 hd2] at h1
  exact ⟨h0, h1⟩

theorem value_u0_ae (O : Opens R3) (ψ : 𝓓((⊤ : Opens R3), ℝ)) {S : Set R3}
    (hS : S ⊆ (O : Set R3)) :
    ⇑(W1p.value (W1p.restrictL (le_top : O ≤ ⊤)
      (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ))) =ᵐ[(volume : Measure R3).restrict S]
      (ψ : R3 → ℝ) := by
  have h1 := ae_restrict_of_ae_restrict_of_subset hS (W1p.value_restrictL_ae (le_top : O ≤ ⊤)
    (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ))
  have h2 := ae_restrict_of_ae_restrict_of_subset (Set.subset_univ S)
    (testFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ⊤) 2 ψ)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, W1p.value_ofTestFunctionₗ, hx2]

theorem ball_source_subset {z : R3} {η : ℝ}
    (hz : closedBall z η ⊆ ball fixedExteriorSourceCenter (1 / 8)) :
    ball z η ⊆ ball (0 : R3) 2 := by
  intro x hx
  have hx' : dist x fixedExteriorSourceCenter < 1 / 8 := hz (ball_subset_closedBall hx)
  have hc : ‖fixedExteriorSourceCenter‖ = 3 / 2 := by
    simp [fixedExteriorSourceCenter]
  rw [mem_ball, dist_zero_right]
  calc ‖x‖ ≤ ‖x - fixedExteriorSourceCenter‖ + ‖fixedExteriorSourceCenter‖ :=
        norm_le_norm_sub_add _ _
    _ < 2 := by rw [← dist_eq_norm, hc]; linarith

/-- The actual L² source approximation on the two smaller balls, with source-zero graphs. -/
theorem approx_two_l2 (hUCP : UniqueContinuation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    {p q z : R3} {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η)
    (hp : closedBall p ρ ⊆ ball (0 : R3) 2) (hq : closedBall q ρ ⊆ ball (0 : R3) 2)
    (hz : closedBall z η ⊆ ball fixedExteriorSourceCenter (1 / 8))
    (hzp : Disjoint (closedBall z η) (closedBall p ρ))
    (hzq : Disjoint (closedBall z η) (closedBall q ρ))
    (ψ : 𝓓((⊤ : Opens R3), ℝ))
    (hψ : ∀ x ∈ ball p ρ ∪ ball q ρ, divCoeffGrad (principalCoefficient g) ψ x = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      (∀ x ∈ ball p (2 * ρ / 3), (f : R3 → ℝ) x = 0) ∧
      (∀ x ∈ ball q (2 * ρ / 3), (f : R3 → ℝ) x = 0) ∧
      (∫ x in ball p (2 * ρ / 3), (W1p.value (Kresp g hg f) x - (ψ : R3 → ℝ) x) ^ 2) < δ ^ 2 ∧
      (∫ x in ball q (2 * ρ / 3), (W1p.value (Kresp g hg f) x - (ψ : R3 → ℝ) x) ^ 2) < δ ^ 2 := by
  set A := principalCoefficient g with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_principalCoefficient g hg
  have hpos : ∀ x, (A x).PosDef := principalCoefficient_posDef g hg
  obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = ρ / 3 := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂def⟩ : ∃ r₂ : ℝ, r₂ = 2 * ρ / 3 := ⟨_, rfl⟩
  have hr₁ : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def, hr₂def]; linarith only [hρ]
  have hr₂ρ : r₂ < ρ := by rw [hr₂def]; linarith only [hρ]
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hpr₂ : closedBall p r₂ ⊆ ball (0 : R3) 2 := (closedBall_subset_closedBall hr₂ρ.le).trans hp
  have hqr₂ : closedBall q r₂ ⊆ ball (0 : R3) 2 := (closedBall_subset_closedBall hr₂ρ.le).trans hq
  have hWsub : ballO z η ≤ fixedExteriorSourceOpens := fun x hx => hz (ball_subset_closedBall hx)
  -- the `L²` Runge approximation on the two balls
  have hcl : closure (ball p r₂ ∪ ball q r₂) = closedBall p r₂ ∪ closedBall q r₂ := by
    rw [closure_union, closure_ball _ hr₂.ne', closure_ball _ hr₂.ne']
  have hO' : IsOpen (ball p ρ ∪ ball q ρ) := isOpen_ball.union isOpen_ball
  have hdisj : ∀ {c : R3}, Disjoint (closedBall z η) (closedBall c ρ) →
      Disjoint (ball z η) (closedBall c r₂) := fun h =>
    h.mono ball_subset_closedBall (closedBall_subset_closedBall hr₂ρ.le)
  obtain ⟨f', hf'⟩ := l2_runge hUCP 0 (by norm_num : (0 : ℝ) < 2) hA hpos
    (W := ballO z η) (U := ball p r₂ ∪ ball q r₂) (U' := ball p ρ ∪ ball q ρ)
    ⟨z, mem_ball_self hη⟩ (ball_source_subset hz)
    (fun f' => Kresp g hg (TestFunction.monoCLM ℝ f'))
    (fun f' => (radiusTwoSourceSolution g hg _).2)
    (fun f' φ hφ => by
      refine (radiusTwoSourceSolution_integral g hg _ φ hφ).trans ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [RungeAux.coe_monoCLM hWsub f']
      rfl)
    (isOpen_ball.union isOpen_ball) hO'
    (by
      rw [hcl]
      exact union_subset_union (closedBall_subset_ball hr₂ρ) (closedBall_subset_ball hr₂ρ))
    (union_subset (ball_subset_closedBall.trans hp) (ball_subset_closedBall.trans hq))
    (by rw [hcl]; exact Disjoint.union_right (hdisj hzp) (hdisj hzq))
    (by rw [hcl]; exact isConnected_ball_diff_two hr₂ hpr₂ hqr₂)
    (W1p.restrictL (le_top : (⟨ball p ρ ∪ ball q ρ, hO'⟩ : Opens R3) ≤ ⊤)
      (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ))
    (weak_testFn hA ⟨ball p ρ ∪ ball q ρ, hO'⟩ ψ hψ) (by positivity : (0 : ℝ) < δ ^ 2)
  -- integrability of the squared error
  have hUM : ball p r₂ ∪ ball q r₂ ⊆ ball (0 : R3) 2 :=
    union_subset (ball_subset_closedBall.trans hpr₂) (ball_subset_closedBall.trans hqr₂)
  have hUO : ball p r₂ ∪ ball q r₂ ⊆ ball p ρ ∪ ball q ρ :=
    union_subset_union (ball_subset_ball hr₂ρ.le) (ball_subset_ball hr₂ρ.le)
  have hInt : IntegrableOn (fun x => (W1p.value (Kresp g hg (TestFunction.monoCLM ℝ f')) x -
      W1p.value (W1p.restrictL (le_top : (⟨ball p ρ ∪ ball q ρ, hO'⟩ : Opens R3) ≤ ⊤)
        (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) x) ^ 2)
      (ball p r₂ ∪ ball q r₂) := by
    have m1 := (Lp.memLp (W1p.value (Kresp g hg (TestFunction.monoCLM ℝ f')))).mono_measure
      (Measure.restrict_mono hUM le_rfl)
    have m2 := (Lp.memLp (W1p.value (W1p.restrictL
      (le_top : (⟨ball p ρ ∪ ball q ρ, hO'⟩ : Opens R3) ≤ ⊤)
        (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)))).mono_measure
      (Measure.restrict_mono hUO le_rfl)
    exact (m1.sub m2).integrable_sq
  -- the `L²` error on each ball
  have hloc : ∀ {c : R3}, ball c r₂ ⊆ ball p r₂ ∪ ball q r₂ → ball c r₂ ⊆ ball p ρ ∪ ball q ρ →
      ∫ x in ball c r₂, (W1p.value (Kresp g hg (TestFunction.monoCLM ℝ f')) x -
        (ψ : R3 → ℝ) x) ^ 2 < δ ^ 2 := by
    intro c hc hc'
    have e : ∫ x in ball c r₂, (W1p.value (Kresp g hg (TestFunction.monoCLM ℝ f')) x -
        (ψ : R3 → ℝ) x) ^ 2 = ∫ x in ball c r₂,
        (W1p.value (Kresp g hg (TestFunction.monoCLM ℝ f')) x -
          W1p.value (W1p.restrictL (le_top : (⟨ball p ρ ∪ ball q ρ, hO'⟩ : Opens R3) ≤ ⊤)
            (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 ψ)) x) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [value_u0_ae ⟨ball p ρ ∪ ball q ρ, hO'⟩ ψ hc'] with x hx
      rw [hx]
    rw [e]
    exact lt_of_le_of_lt (setIntegral_mono_set hInt
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.eventuallyLE) hf'
  have hf0 : ∀ {c : R3}, Disjoint (closedBall z η) (closedBall c ρ) →
      ∀ x ∈ ball c r₂, ((TestFunction.monoCLM ℝ f' : 𝓓(fixedExteriorSourceOpens, ℝ)) :
        R3 → ℝ) x = 0 := by
    intro c hc x hx
    rw [RungeAux.coe_monoCLM hWsub f']
    refine RungeAux.eq_zero_of_notMem f' fun hxz => ?_
    exact Set.disjoint_left.mp (hdisj hc) hxz (ball_subset_closedBall hx)
  rw [← hr₂def]
  exact ⟨TestFunction.monoCLM ℝ f', hf0 hzp, hf0 hzq,
    hloc subset_union_left (subset_union_left.trans hUO),
    hloc subset_union_right (subset_union_right.trans hUO)⟩

/-- **Two-point approximation.** With sources in a small ball `ball z η` inside the fixed source
ball, away from two small target balls, a compactly supported smooth `ψ` solving the equation on
the target balls is matched, up to `ε`, in value and gradient at `p` and in value at `q`. -/
theorem approx_two (hUCP : UniqueContinuation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ)
    (hresp : IsRadiusTwoSmoothSourceResponse g hg response)
    {p q z : R3} {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η)
    (hp : closedBall p ρ ⊆ ball (0 : R3) 2) (hq : closedBall q ρ ⊆ ball (0 : R3) 2)
    (hz : closedBall z η ⊆ ball fixedExteriorSourceCenter (1 / 8))
    (hzp : Disjoint (closedBall z η) (closedBall p ρ))
    (hzq : Disjoint (closedBall z η) (closedBall q ρ))
    (ψ : 𝓓((⊤ : Opens R3), ℝ))
    (hψ : ∀ x ∈ ball p ρ ∪ ball q ρ, divCoeffGrad (principalCoefficient g) ψ x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ), |response f p - ψ p| < ε ∧
      ‖fderiv ℝ (response f) p - fderiv ℝ (ψ : R3 → ℝ) p‖ < ε ∧
      |response f q - ψ q| < ε := by
  set A := principalCoefficient g with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_principalCoefficient g hg
  have hpos : ∀ x, (A x).PosDef := principalCoefficient_posDef g hg
  obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = ρ / 3 := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂def⟩ : ∃ r₂ : ℝ, r₂ = 2 * ρ / 3 := ⟨_, rfl⟩
  have hr₁ : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₁₂ : r₁ < r₂ := by rw [hr₁def, hr₂def]; linarith only [hρ]
  have hr₂ρ : r₂ < ρ := by rw [hr₂def]; linarith only [hρ]
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hpr₂ : closedBall p r₂ ⊆ ball (0 : R3) 2 := (closedBall_subset_closedBall hr₂ρ.le).trans hp
  have hqr₂ : closedBall q r₂ ⊆ ball (0 : R3) 2 := (closedBall_subset_closedBall hr₂ρ.le).trans hq
  obtain ⟨Cp, hCp, hestp⟩ := jet_bound g hg response hresp p hr₁ hr₁₂ hpr₂
  obtain ⟨Cq, hCq, hestq⟩ := jet_bound g hg response hresp q hr₁ hr₁₂ hqr₂
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 * (Cp + Cq + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδε : (Cp + Cq + 1) * δ = ε / 2 := by
    rw [hδdef]; field_simp
  have hsmall : ∀ C : ℝ, C ≤ Cp + Cq → C * δ < ε := fun C hC => by
    have : C * δ ≤ (Cp + Cq) * δ := mul_le_mul_of_nonneg_right hC hδ.le
    nlinarith only [this, hδε, hδ, hε]
  obtain ⟨f, hf0p, hf0q, hintp, hintq⟩ := approx_two_l2 hUCP g hg hρ hη
    hp hq hz hzp hzq ψ hψ hδ
  rw [← hr₂def] at hf0p hf0q hintp hintq
  obtain ⟨bp0, bp1⟩ := hestp f ψ hf0p
    (fun x hx => hψ x (Or.inl (ball_subset_ball hr₂ρ.le hx))) δ hδ hintp
  obtain ⟨bq0, -⟩ := hestq f ψ hf0q
    (fun x hx => hψ x (Or.inr (ball_subset_ball hr₂ρ.le hx))) δ hδ hintq
  exact ⟨f, bp0.trans_lt (hsmall Cp (by linarith only [hCq])),
    bp1.trans_lt (hsmall Cp (by linarith only [hCq])),
    bq0.trans_lt (hsmall Cq (by linarith only [hCp]))⟩

/-- A smooth compactly supported function as a test function on all of `R3`. -/
def testOf (φ : R3 → ℝ) (h : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    𝓓((⊤ : Opens R3), ℝ) :=
  ⟨φ, h, hc, fun _ _ => trivial⟩

theorem coe_testOf (φ : R3 → ℝ) (h : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ((testOf φ h hc : 𝓓((⊤ : Opens R3), ℝ)) : R3 → ℝ) = φ := rfl

theorem divCoeffGrad_of_eqOn {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {ψ : R3 → ℝ} {s : Set R3}
    (hs : IsOpen s) (c : ℝ) (h : ∀ x ∈ s, ψ x = c) : ∀ x ∈ s, divCoeffGrad A ψ x = 0 :=
  fun x hx => by
    rw [divCoeffGrad_congr (h := fun _ => c) (Filter.eventually_of_mem (hs.mem_nhds hx) h),
      divCoeffGrad_const]

/-- A small source ball inside the fixed source ball, away from two given points. -/
theorem exists_source_ball (p q : R3) : ∃ z : R3, ∃ η : ℝ, 0 < η ∧
    closedBall z η ⊆ ball fixedExteriorSourceCenter (1 / 8) ∧ 2 * η < dist z p ∧
    2 * η < dist z q := by
  have hinf : (ball fixedExteriorSourceCenter (1 / 8 : ℝ)).Infinite :=
    infinite_of_mem_nhds fixedExteriorSourceCenter (ball_mem_nhds _ (by norm_num))
  obtain ⟨z, hz, hzpq⟩ := (hinf.sdiff (Set.toFinite {p, q})).nonempty
  have hzp : z ≠ p := fun h => hzpq (by simp [h])
  have hzq : z ≠ q := fun h => hzpq (by simp [h])
  have hz' : dist z fixedExteriorSourceCenter < 1 / 8 := hz
  have h1 : 0 < dist z p := dist_pos.2 hzp
  have h2 : 0 < dist z q := dist_pos.2 hzq
  refine ⟨z, min (1 / 8 - dist z fixedExteriorSourceCenter) (min (dist z p) (dist z q)) / 3,
    by positivity, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : dist x z ≤ _ := hx
    have hm := min_le_left (1 / 8 - dist z fixedExteriorSourceCenter) (min (dist z p) (dist z q))
    have hd := dist_triangle x z fixedExteriorSourceCenter
    have hmp : 0 < min (1 / 8 - dist z fixedExteriorSourceCenter) (min (dist z p) (dist z q)) :=
      by positivity
    show dist x fixedExteriorSourceCenter < 1 / 8
    linarith only [hx', hm, hd, hmp]
  · have hm := (min_le_right (1 / 8 - dist z fixedExteriorSourceCenter)
      (min (dist z p) (dist z q))).trans (min_le_left _ _)
    have hmp : 0 < min (1 / 8 - dist z fixedExteriorSourceCenter) (min (dist z p) (dist z q)) :=
      by positivity
    linarith only [hm, hmp]
  · have hm := (min_le_right (1 / 8 - dist z fixedExteriorSourceCenter)
      (min (dist z p) (dist z q))).trans (min_le_right _ _)
    have hmp : 0 < min (1 / 8 - dist z fixedExteriorSourceCenter) (min (dist z p) (dist z q)) :=
      by positivity
    linarith only [hm, hmp]

theorem closedBall_sub_two {p : R3} {ρ : ℝ} (hp : p ∈ ball (0 : R3) 2) (hρ : ρ ≤ (2 - ‖p‖) / 2) :
    closedBall p ρ ⊆ ball (0 : R3) 2 := by
  intro x hx
  have hp' : ‖p‖ < 2 := by simpa using hp
  have hx' : dist x p ≤ ρ := hx
  rw [mem_ball, dist_zero_right]
  have := norm_le_norm_sub_add x p
  rw [← dist_eq_norm] at this
  linarith only [this, hx', hρ, hp']

/-- **Value separation.** -/
theorem separate (hUCP : UniqueContinuation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ)
    (hresp : IsRadiusTwoSmoothSourceResponse g hg response)
    {p q : R3} (hp : p ∈ ball (0 : R3) 2) (hq : q ∈ closedBall (0 : R3) 2) (hpq : p ≠ q) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ), response f p ≠ response f q := by
  obtain ⟨z, η, hη, hz, hzp, hzq⟩ := exists_source_ball p q
  have hp' : ‖p‖ < 2 := by simpa using hp
  by_cases hq2 : ‖q‖ = 2
  · -- the boundary point: responses vanish there
    set ρ := min ((2 - ‖p‖) / 2) η with hρdef
    have hρ : 0 < ρ := lt_min (by linarith only [hp']) hη
    let b : ContDiffBump p := ⟨ρ, 2 * ρ, hρ, by linarith only [hρ]⟩
    let ψ := testOf (fun y => b y) b.contDiff b.hasCompactSupport
    have hψ1 : ∀ x ∈ ball p ρ, (ψ : R3 → ℝ) x = 1 := fun x hx =>
      b.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hdisj : Disjoint (closedBall z η) (closedBall p ρ) :=
      closedBall_disjoint_closedBall (by
        have := min_le_right ((2 - ‖p‖) / 2) η
        linarith only [this, hzp])
    obtain ⟨f, hf, -, -⟩ := approx_two hUCP g hg response hresp hρ hη
      (closedBall_sub_two hp (min_le_left _ _)) (closedBall_sub_two hp (min_le_left _ _)) hz
      hdisj hdisj ψ (fun x hx => divCoeffGrad_of_eqOn (isOpen_ball.union isOpen_ball) 1
        (fun y hy => hψ1 y (by simpa using hy)) x hx) (by norm_num : (0 : ℝ) < 1 / 2)
    refine ⟨f, ?_⟩
    rw [(hresp f).2.2.2 q hq2, hψ1 p (mem_ball_self hρ)] at *
    intro h
    rw [h] at hf
    norm_num at hf
  · have hq' : ‖q‖ < 2 := lt_of_le_of_ne (by simpa using hq) hq2
    have hq'' : q ∈ ball (0 : R3) 2 := by simpa using hq'
    have hd : 0 < dist p q := dist_pos.2 hpq
    set ρ := min (min ((2 - ‖p‖) / 2) ((2 - ‖q‖) / 2)) (min η (dist p q / 4)) with hρdef
    have hρ : 0 < ρ := lt_min (lt_min (by linarith only [hp']) (by linarith only [hq']))
      (lt_min hη (by positivity))
    have hρ1 : ρ ≤ (2 - ‖p‖) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hρ2 : ρ ≤ (2 - ‖q‖) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hρ3 : ρ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
    have hρ4 : ρ ≤ dist p q / 4 := (min_le_right _ _).trans (min_le_right _ _)
    let b : ContDiffBump p := ⟨ρ, 2 * ρ, hρ, by linarith only [hρ]⟩
    let ψ := testOf (fun y => b y) b.contDiff b.hasCompactSupport
    have hψ1 : ∀ x ∈ ball p ρ, (ψ : R3 → ℝ) x = 1 := fun x hx =>
      b.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hψ0 : ∀ x ∈ ball q ρ, (ψ : R3 → ℝ) x = 0 := fun x hx => by
      refine b.zero_of_le_dist ?_
      have hx' : dist x q < ρ := hx
      have := dist_triangle p x q
      rw [dist_comm p x] at this
      show 2 * ρ ≤ dist x p
      linarith only [this, hx', hρ4, hd]
    have hψ : ∀ x ∈ ball p ρ ∪ ball q ρ, divCoeffGrad (principalCoefficient g) ψ x = 0 := by
      rintro x (hx | hx)
      · exact divCoeffGrad_of_eqOn isOpen_ball 1 hψ1 x hx
      · exact divCoeffGrad_of_eqOn isOpen_ball 0 hψ0 x hx
    obtain ⟨f, hfp, -, hfq⟩ := approx_two hUCP g hg response hresp hρ hη
      (closedBall_sub_two hp hρ1) (closedBall_sub_two hq'' hρ2) hz
      (closedBall_disjoint_closedBall (by linarith only [hzp, hρ3]))
      (closedBall_disjoint_closedBall (by linarith only [hzq, hρ3])) ψ hψ
      (by norm_num : (0 : ℝ) < 1 / 2)
    refine ⟨f, fun h => ?_⟩
    rw [hψ1 p (mem_ball_self hρ)] at hfp
    rw [hψ0 q (mem_ball_self hρ)] at hfq
    rw [h] at hfp
    have h1 := abs_lt.1 hfp
    have h2 := abs_lt.1 hfq
    linarith only [h1.1, h2.2]

/-- The symmetric bilinear form `(v, w) ↦ v₀ w₀`. -/
def H0 : R3 →L[ℝ] (R3 →L[ℝ] ℝ) :=
  (EuclideanSpace.proj (0 : Fin 3) : R3 →L[ℝ] ℝ).smulRight
    (EuclideanSpace.proj (0 : Fin 3) : R3 →L[ℝ] ℝ)

theorem H0_apply (v w : R3) : H0 v w = v 0 * w 0 := by
  simp [H0]

theorem jetFunctional_smul_H0 (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : R3) (ξ : R3 →L[ℝ] ℝ)
    (s : ℝ) : jetFunctional A p ξ (s • H0) = jetFunctional A p ξ 0 + s * A p 0 0 := by
  simp [jetFunctional, H0_apply, Fin.sum_univ_three]
  ring

/-- Every covector is the gradient at `p` of a compactly supported smooth function solving the
equation near `p`. -/
theorem exists_test_grad {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) (p : R3) :
    ∃ ρ > 0, ∀ ξ : R3 →L[ℝ] ℝ, ∃ ψ : 𝓓((⊤ : Opens R3), ℝ),
      (∀ x ∈ ball p ρ, divCoeffGrad A ψ x = 0) ∧ fderiv ℝ (ψ : R3 → ℝ) p = ξ := by
  obtain ⟨ρ₀, hρ₀, hloc⟩ := exists_local_solution_jet hA hpos p
  refine ⟨ρ₀ / 4, by positivity, fun ξ => ?_⟩
  have hA00 : 0 < A p 0 0 := (hpos p).diag_pos
  set s : ℝ := -jetFunctional A p ξ 0 / A p 0 0 with hs
  have hJ : jetFunctional A p ξ (s • H0) = 0 := by
    rw [jetFunctional_smul_H0, hs]
    field_simp
    ring
  have hsym : ∀ v w : R3, (s • H0) v w = (s • H0) w v := fun v w => by
    simp [H0_apply, mul_comm (v 0)]
  obtain ⟨u, hu, hue, -, hu1, -⟩ := hloc 0 ξ (s • H0) hsym hJ
  let χ : ContDiffBump p := ⟨ρ₀ / 4, ρ₀ / 2, by positivity, by linarith only [hρ₀]⟩
  let φ : R3 → ℝ := fun z => χ z * u z
  have hχts : tsupport (χ : R3 → ℝ) ⊆ ball p ρ₀ := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (by simp [χ]; linarith only [hρ₀])
  have hφ : ContDiff ℝ ∞ φ := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball p ρ₀
    · exact χ.contDiff.contDiffAt.mul (hu.contDiffAt (isOpen_ball.mem_nhds hy))
    · have hy' : y ∉ tsupport (χ : R3 → ℝ) := fun h => hy (hχts h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy'] with z hz
      simp [φ, image_eq_zero_of_notMem_tsupport hz]
  have hφc : HasCompactSupport φ := χ.hasCompactSupport.mul_right
  have hφu : ∀ y ∈ ball p (ρ₀ / 4), φ =ᶠ[𝓝 y] u := by
    intro y hy
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp [φ, χ.one_of_mem_closedBall (ball_subset_closedBall hz)]
  refine ⟨testOf φ hφ hφc, fun x hx => ?_, ?_⟩
  · rw [coe_testOf, divCoeffGrad_congr (hφu x hx)]
    exact hue x (ball_subset_ball (by linarith only [hρ₀]) hx)
  · rw [coe_testOf, (hφu p (mem_ball_self (by positivity))).fderiv_eq, hu1]

/-- Responses are linear at the level of gradients at interior points. -/
theorem fderiv_response_add_smul (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ)
    (hresp : IsRadiusTwoSmoothSourceResponse g hg response) {p : R3}
    (hp : p ∈ ball (0 : R3) 2) (a : ℝ) (f₁ f₂ : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    fderiv ℝ (response (a • f₁ + f₂)) p =
      a • fderiv ℝ (response f₁) p + fderiv ℝ (response f₂) p := by
  have hA : ContDiff ℝ ∞ (principalCoefficient g) := contDiff_principalCoefficient g hg
  have hpos := principalCoefficient_posDef g hg
  have hK : Kresp g hg (a • f₁ + f₂) = a • Kresp g hg f₁ + Kresp g hg f₂ :=
    RungeAux.K_add_smul 0 (by norm_num : (0 : ℝ) < 2) hA.continuous hpos (Kresp g hg)
      (fun f => (radiusTwoSourceSolution g hg _).2)
      (fun f φ hφ => radiusTwoSourceSolution_integral g hg _ φ hφ) a f₁ f₂
  have hv : W1p.value (Kresp g hg (a • f₁ + f₂)) =
      a • W1p.value (Kresp g hg f₁) + W1p.value (Kresp g hg f₂) := by
    rw [hK]; simp only [← W1p.valueL_apply, map_add, map_smul]
  have hae : response (a • f₁ + f₂) =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) 2)]
      fun x => a * response f₁ x + response f₂ x := by
    filter_upwards [(hresp (a • f₁ + f₂)).2.2.1, (hresp f₁).2.2.1, (hresp f₂).2.2.1,
      Lp.coeFn_add (a • W1p.value (Kresp g hg f₁)) (W1p.value (Kresp g hg f₂)),
      Lp.coeFn_smul a (W1p.value (Kresp g hg f₁))] with x h0 h1 h2 h3 h4
    have e : W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨((a • f₁ + f₂ : 𝓓(fixedExteriorSourceOpens, ℝ)) : R3 → ℝ), (a • f₁ + f₂).contDiff⟩) :
          RadiusTwoH1) = W1p.value (Kresp g hg (a • f₁ + f₂)) := rfl
    rw [h0, e, hv]
    erw [h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2, smul_eq_mul]
    all_goals rfl
  have hc : ∀ f, ContinuousOn (response f) (ball (0 : R3) 2) := fun f =>
    (hresp f).1.continuousOn
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball (hc _)
    (((hc f₁).const_smul a).add (hc f₂))
  have hev : response (a • f₁ + f₂) =ᶠ[𝓝 p] fun x => a * response f₁ x + response f₂ x :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hp) heq
  have hd : ∀ f, DifferentiableAt ℝ (response f) p := fun f =>
    ((hresp f).1.contDiffAt (isOpen_ball.mem_nhds hp)).differentiableAt (by simp)
  rw [hev.fderiv_eq]
  exact (((hd f₁).hasFDerivAt.const_mul a).add (hd f₂).hasFDerivAt).fderiv

/-- **Gradient surjectivity.** -/
theorem gradient_surj (hUCP : UniqueContinuation) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (response : 𝓓(fixedExteriorSourceOpens, ℝ) → R3 → ℝ)
    (hresp : IsRadiusTwoSmoothSourceResponse g hg response) {p : R3}
    (hp : p ∈ ball (0 : R3) 2) (ξ : R3 →L[ℝ] ℝ) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ), fderiv ℝ (response f) p = ξ := by
  have hlin := fderiv_response_add_smul g hg response hresp hp
  have hzero : fderiv ℝ (response 0) p = 0 := by
    have h := hlin 1 0 0
    simp only [one_smul, add_zero] at h
    exact add_eq_left.mp h.symm
  let S : Submodule ℝ (R3 →L[ℝ] ℝ) :=
    { carrier := Set.range fun f => fderiv ℝ (response f) p
      add_mem' := by
        rintro _ _ ⟨f₁, rfl⟩ ⟨f₂, rfl⟩
        exact ⟨(1 : ℝ) • f₁ + f₂, by beta_reduce; rw [hlin, one_smul]⟩
      zero_mem' := ⟨0, hzero⟩
      smul_mem' := by
        rintro c _ ⟨f, rfl⟩
        exact ⟨c • f + 0, by beta_reduce; rw [hlin, hzero, add_zero]⟩ }
  have hS : IsClosed (S : Set (R3 →L[ℝ] ℝ)) := S.closed_of_finiteDimensional
  have hA : ContDiff ℝ ∞ (principalCoefficient g) := contDiff_principalCoefficient g hg
  have hpos := principalCoefficient_posDef g hg
  obtain ⟨ρ₀, hρ₀, hψ⟩ := exists_test_grad hA hpos p
  obtain ⟨ψ, hψe, hψξ⟩ := hψ ξ
  obtain ⟨z, η, hη, hz, hzp, -⟩ := exists_source_ball p p
  have hp' : ‖p‖ < 2 := by simpa using hp
  set ρ := min ((2 - ‖p‖) / 2) (min η ρ₀) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith only [hp']) (lt_min hη hρ₀)
  have hρ1 : ρ ≤ (2 - ‖p‖) / 2 := min_le_left _ _
  have hρ3 : ρ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ ρ₀ := (min_le_right _ _).trans (min_le_right _ _)
  have hdisj : Disjoint (closedBall z η) (closedBall p ρ) :=
    closedBall_disjoint_closedBall (by linarith only [hzp, hρ3])
  have hmem : ξ ∈ closure (S : Set (R3 →L[ℝ] ℝ)) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨f, -, hf, -⟩ := approx_two hUCP g hg response hresp hρ hη
      (closedBall_sub_two hp hρ1) (closedBall_sub_two hp hρ1) hz hdisj hdisj ψ
      (fun x hx => hψe x (by
        rcases hx with hx | hx <;> exact ball_subset_ball hρ4 hx)) hε
    refine ⟨fderiv ℝ (response f) p, ⟨f, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm, ← hψξ]
    exact hf
  rw [hS.closure_eq] at hmem
  exact hmem

end OAI.AnisotropicCalderon.ExteriorSource.Literature.SepAux

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature
open EnergyBridge DirichletFamily MetricVolume TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine

open SepAux in
/-- **Task 09**, conditional on weak unique continuation. -/
theorem radiusTwoSourceSeparation_of_uniqueContinuation (hUCP : UniqueContinuation) :
    RadiusTwoSourceSeparation := by
  intro g hg response hresp
  exact ⟨fun p hp q hq hpq => separate hUCP g hg response hresp hp hq hpq,
    fun p hp ξ => gradient_surj hUCP g hg response hresp hp ξ⟩

end OAI.AnisotropicCalderon.ExteriorSource.Literature
