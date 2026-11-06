import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17
import Calderon.CollaboratorSmoothRepOct17
import Calderon.CollaboratorLocalJetsCalcOct17
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Sobolev helpers for `LocalJets` (Lassas–Liimatainen–Salo, Prop. A.5): the weak equation
against test functions, smooth integration by parts, qualitative regularity to all orders and
smooth representatives, embedding smooth functions in `W^{k,2}(B)` with bounds, the perturbation
operator `w ↦ div(M ∇w)`, and the constant-coefficient a priori bound. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric Set
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.Jets
open TauCeti TauCeti.PDE EnergyBridge

/-- The weak equation `-div(a ∇u) = F` on `B`, tested against test functions. -/
def WeakEq (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (F : R3 → ℝ)
    (u : W1p (volume : Measure R3) ballOpens 2) : Prop :=
  ∀ φ : 𝓓(ballOpens, ℝ),
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient u x) = ∫ x in (ballOpens : Set R3), F x * φ x


/-! ### Auxiliary lemmas -/

section Generic
variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

theorem weakEq_of_isWeakSolution_generic {F : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 F u) (φ : 𝓓(Omega, ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (gradient (φ : EuclideanSpace ℝ ι → ℝ) x)
        (W1p.gradient (u : W1p mu Omega 2) x) ∂mu = ∫ x in Omega, F x * φ x ∂mu := by
  have h := hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (p := 2) φ⟩
  rw [energyFormH1_def, dirichletForcing_apply_eq_setIntegral] at h
  refine (integral_congr_ae ?_).trans (h.trans (integral_congr_ae ?_))
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    simp [energyIntegrand_apply]
    rw [hx]
  · filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]

end Generic

theorem integrable_mbf_test {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a)
    (G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) (φ : 𝓓(ballOpens, ℝ)) :
    Integrable (fun x => matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (G x))
      ((volume : Measure R3).restrict ballOpens) := by
  refine (integrable_mbf ha G (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ)).congr ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ] with x hx
  rw [hx]

theorem integrable_lp_mul_test (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (φ : 𝓓(ballOpens, ℝ)) :
    Integrable (fun x => F x * φ x) ((volume : Measure R3).restrict ballOpens) :=
  HO.integrable_mul_test (HO.aeIn_of_mem (HO.mem_Hs_zero F)) φ

theorem fderiv_test_eq_zero (φ : 𝓓(ballOpens, ℝ)) {x : R3} (hx : x ∉ (ballOpens : Set R3)) :
    fderiv ℝ (φ : R3 → ℝ) x = 0 :=
  fderiv_of_notMem_tsupport ℝ fun hmem => hx (φ.tsupport_subset hmem)

theorem test_eq_zero (φ : 𝓓(ballOpens, ℝ)) {x : R3} (hx : x ∉ (ballOpens : Set R3)) :
    (φ : R3 → ℝ) x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)

theorem ibp_row {h : R3 → ℝ} (hh : ContDiffOn ℝ 1 h B) (φ : 𝓓(ballOpens, ℝ)) (i : Fin 3) :
    ∫ x, fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) * h x =
      -∫ x, fderiv ℝ h x (EuclideanSpace.single i 1) * φ x := by
  have hB : IsOpen (ballOpens : Set R3) := ballOpens.isOpen
  have hd : HasWeakFDerivOn volume ballOpens h (fderiv ℝ h) :=
    hasWeakFDerivOn_of_differentiableOn
      (hh.continuousOn.locallyIntegrableOn hB.measurableSet)
      ((hh.continuousOn_fderiv_of_isOpen hB le_rfl).locallyIntegrableOn hB.measurableSet)
      (fun x hx => (hh.differentiableOn (by norm_num) x hx).differentiableAt (hB.mem_nhds hx))
  have := (hd.hasWeakLineDerivOn (EuclideanSpace.single i 1)).integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [smul_eq_mul] at this
  have e1 : ∀ x, lineDeriv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) =
      fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) := fun x =>
    ((φ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv
  simp only [e1] at this
  rw [this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_comm]

/-! ### Existence -/

theorem exists_weakEq {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a) {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ∃ u : W1p (volume : Measure R3) ballOpens 2,
      u ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 ∧ WeakEq a F u := by
  have ham : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens) :=
    have ha' : @Continuous R3 (Fin 3 → Fin 3 → ℝ) _ _ a := ha
    ha'.aestronglyMeasurable
  obtain ⟨u, hu, -⟩ := UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball (n := 2)
    (Omega := ballOpens) (a := a) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (beta := 0) (gamma := 0) hell ham aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => le_rfl) (z := 0) (R := 1) zero_le_one (fun x hx => hx)
    (by simpa using hell.1) F
  exact ⟨u, u.2, weakEq_of_isWeakSolution_generic hu⟩

/-! ### Regularity and smooth representatives -/

theorem value_mem_Hs_all {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (hsmooth : ContDiff ℝ ∞ a)
    (hell : UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)} (hF : ∀ m, F ∈ HO.Hs m)
    {u : W1p (volume : Measure R3) ballOpens 2}
    (hu0 : u ∈ w1p0Submodule (volume : Measure R3) ballOpens 2) (hu : WeakEq a F u) (m : ℕ) :
    W1p.value u ∈ HO.Hs m := by
  have hreg : ∀ m, HO.RegAt a m := fun m =>
    Nat.rec (HO.regAt_zero hsmooth.contDiffOn hell)
      (fun m ih => HO.regAt_succ hsmooth.contDiffOn hell m ih) m
  have h := hreg m F (hF m) u hu0 fun φ hφ =>
    eq_of_testFunction hsmooth.continuous (G := W1p.gradient u) (F := F) hu φ hφ
  exact HO.Hs_le (by omega) h

theorem exists_smooth_rep {u : W1p (volume : Measure R3) ballOpens 2}
    (hu : ∀ m, W1p.value u ∈ HO.Hs m) :
    ∃ w : R3 → ℝ, ContDiffOn ℝ ∞ w B ∧
      w =ᵐ[(volume : Measure R3).restrict ballOpens] W1p.value u := by
  refine exists_contDiffOn_ae_eq (O := B) isOpen_ball (w := W1p.value u) fun x hx => ?_
  have hx' : ‖x‖ < 1 := by simpa [B] using hx
  have hsub : ball x (1 - ‖x‖) ⊆ B := fun y hy => by
    have : dist y x < 1 - ‖x‖ := hy
    simp only [B, mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' y x
    rw [dist_eq_norm] at *
    linarith [norm_sub_rev y x]
  refine ⟨1 - ‖x‖, by linarith, hsub, fun k => ?_⟩
  obtain ⟨G, hG⟩ := HO.mem_Hs.mp (hu k)
  have hU : (⟨ball x (1 - ‖x‖), isOpen_ball⟩ : Opens R3) ≤ ballOpens := hsub
  refine ⟨Wkp.restrictL hU k G, ?_⟩
  have := Wkp.value_restrictL_ae (mu := (volume : Measure R3)) (p := 2) hU k G
  rw [hG] at this
  exact this

theorem gradient_ae_eq_of_smooth {u : W1p (volume : Measure R3) ballOpens 2} {w : R3 → ℝ}
    (hw : ContDiffOn ℝ ∞ w B)
    (hwu : w =ᵐ[(volume : Measure R3).restrict ballOpens] W1p.value u) :
    ⇑(W1p.gradient u) =ᵐ[(volume : Measure R3).restrict ballOpens] gradient w := by
  have hv1 : Wkp.value 1 (u : Wkp (volume : Measure R3) ballOpens 2 1) = W1p.value u :=
    Wkp.value_one _
  have hg1 : Wkp.iteratedGradient 0 (u : Wkp (volume : Measure R3) ballOpens 2 1) =
      W1p.gradient u := Wkp.iteratedGradient_zero _
  have h := Wkp.iteratedGradient_ae_eq_of_contDiffOn (mu := (volume : Measure R3))
    (Omega := ballOpens) (p := 2) 0 (u : Wkp (volume : Measure R3) ballOpens 2 1) (f := w)
    (hw.of_le (by simp)) (by erw [hv1]; exact hwu.symm)
  erw [hg1, iteratedGradientChain_zero] at h
  exact h

/-! ### Smooth integration by parts -/

theorem integral_mbf_smooth {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {v : R3 → ℝ} (hv : ContDiffOn ℝ ∞ v B) (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
        (gradient v x) = -∫ x in (ballOpens : Set R3), divCoeffGrad a v x * φ x := by
  have hB : IsOpen (ballOpens : Set R3) := ballOpens.isOpen
  set h : Fin 3 → R3 → ℝ := fun i z => ∑ j : Fin 3, a z i j * fderiv ℝ v z (EuclideanSpace.single j 1)
    with hh_def
  have hv1 : ContDiffOn ℝ ∞ (fderiv ℝ v) B := hv.fderiv_of_isOpen isOpen_ball (by simp)
  have hh : ∀ i, ContDiffOn ℝ 1 (h i) B := fun i => by
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
    · exact ((TangH2.contDiff_entry ha i j).of_le (by simp)).contDiffOn
    · exact ((hv1.clm_apply contDiffOn_const).of_le (by simp))
  have hcont : ∀ i, ContinuousOn (fun x => fderiv ℝ (h i) x (EuclideanSpace.single i 1)) B := fun i =>
    ((hh i).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  have hint : ∀ i, Integrable (fun x => fderiv ℝ (h i) x (EuclideanSpace.single i 1) * φ x) := by
    intro i
    have := integrable_smul_of_locallyIntegrableOn (μ := (volume : Measure R3))
      ((hcont i).locallyIntegrableOn hB.measurableSet) φ
    simpa only [smul_eq_mul, mul_comm] using this
  have hint2 : ∀ i, Integrable (fun x => fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) * h i x) := by
    intro i
    have := integrable_lineDeriv_smul_of_locallyIntegrableOn (μ := (volume : Measure R3))
      ((hh i).continuousOn.locallyIntegrableOn hB.measurableSet) φ (EuclideanSpace.single i 1)
    simp only [smul_eq_mul] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [((φ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [show gradient (φ : R3 → ℝ) x = 0 by simp [gradient, fderiv_test_eq_zero φ hx]]; simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [test_eq_zero φ hx, mul_zero])]
  have e1 : (fun x => matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient v x)) =
      fun x => ∑ i : Fin 3, fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) * h i x := by
    funext x
    rw [HO.matrixBilinearForm_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [DiffEq.gradient_coord, DiffEq.pd, DiffEq.e, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, integral_finsetSum _ (fun i _ => hint2 i)]
  simp only [fun i => ibp_row (hh i) φ i]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hint i)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [divCoeffGrad, Finset.sum_mul, h]

theorem continuousOn_divCoeffGrad {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {v : R3 → ℝ} (hv : ContDiffOn ℝ ∞ v B) : ContinuousOn (divCoeffGrad a v) B := by
  have hv1 : ContDiffOn ℝ ∞ (fderiv ℝ v) B := hv.fderiv_of_isOpen isOpen_ball (by simp)
  have hh : ∀ i, ContDiffOn ℝ 1
      (fun z => ∑ j : Fin 3, a z i j * fderiv ℝ v z (EuclideanSpace.single j 1)) B := fun i => by
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ ?_
    · exact ((TangH2.contDiff_entry ha i j).of_le (by simp)).contDiffOn
    · exact ((hv1.clm_apply contDiffOn_const).of_le (by simp))
  have : divCoeffGrad a v = fun x => ∑ i : Fin 3, fderiv ℝ
      (fun z => ∑ j : Fin 3, a z i j * fderiv ℝ v z (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) := rfl
  rw [this]
  exact continuousOn_finsetSum _ fun i _ =>
    ((hh i).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const

theorem divCoeffGrad_eq_zero_of_weak {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {v : R3 → ℝ} (hv : ContDiffOn ℝ ∞ v B)
    (h : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient v x) = 0) :
    ∀ y ∈ B, divCoeffGrad a v y = 0 := by
  have hc := continuousOn_divCoeffGrad ha hv
  have hz := SD.ae_zero_of_integral (g := divCoeffGrad a v)
    (hc.locallyIntegrableOn ballOpens.isOpen.measurableSet) fun φ => by
      have h1 := (h φ).symm.trans (integral_mbf_smooth ha hv φ)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [test_eq_zero φ hx, mul_zero])] at h1
      have h2 : ∫ x, φ x * divCoeffGrad a v x = ∫ x, divCoeffGrad a v x * φ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      rw [h2]; linarith
  exact Measure.eqOn_open_of_ae_eq hz isOpen_ball hc continuousOn_const

/-! ### Combining equations -/

theorem weakEq_sub_pert {a M : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a)
    (hM : Continuous M) {F G : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {u : W1p (volume : Measure R3) ballOpens 2} (hu : WeakEq a F u)
    (hG : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u x) =
        -∫ x in (ballOpens : Set R3), G x * φ x) :
    WeakEq (fun x => a x - M x) (F + G : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) u := by
  intro φ
  have e1 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x - M x) (gradient (φ : R3 → ℝ) x)
      (W1p.gradient u x) = (∫ x in (ballOpens : Set R3), matrixBilinearForm (a x)
        (gradient (φ : R3 → ℝ) x) (W1p.gradient u x)) - ∫ x in (ballOpens : Set R3),
          matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u x) := by
    rw [← integral_sub (integrable_mbf_test ha _ φ) (integrable_mbf_test hM _ φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [matrixBilinearForm_apply, Matrix.sub_mulVec, dotProduct_sub]
  have e2 : ∫ x in (ballOpens : Set R3), (F + G : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x * φ x
      = (∫ x in (ballOpens : Set R3), F x * φ x) + ∫ x in (ballOpens : Set R3), G x * φ x := by
    rw [← integral_add (integrable_lp_mul_test F φ) (integrable_lp_mul_test G φ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add F G] with x hx
    rw [hx, Pi.add_apply, add_mul]
  rw [e1, e2, hu φ, hG φ, sub_neg_eq_add]

theorem divCoeffGrad_eq_zero_of_sum {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {q : R3 → ℝ} (hq : ContDiff ℝ ∞ q) {g : R3 → ℝ} (hqg : ∀ y ∈ B, divCoeffGrad a q y = g y)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (hFg : ⇑F =ᵐ[(volume : Measure R3).restrict ballOpens] g)
    {u : W1p (volume : Measure R3) ballOpens 2} (hu : WeakEq a F u)
    {w : R3 → ℝ} (hw : ContDiffOn ℝ ∞ w B)
    (hwu : w =ᵐ[(volume : Measure R3).restrict ballOpens] W1p.value u) :
    ∀ y ∈ B, divCoeffGrad a (fun y => q y + w y) y = 0 := by
  have hB : IsOpen (ballOpens : Set R3) := ballOpens.isOpen
  refine divCoeffGrad_eq_zero_of_weak ha (hq.contDiffOn.add hw) fun φ => ?_
  have hgw := gradient_ae_eq_of_smooth hw hwu
  have hqm : MemLp (gradient q) 2 ((volume : Measure R3).restrict ballOpens) :=
    memLp_two_restrict_ball_of_continuous (hq.gradient_right (m := 0) (by simp)).continuous
  have iq : Integrable (fun x => matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient q x))
      ((volume : Measure R3).restrict ballOpens) := by
    refine (integrable_mbf_test ha.continuous (hqm.toLp _) φ).congr ?_
    filter_upwards [hqm.coeFn_toLp] with x hx
    rw [hx]
  have iw : Integrable (fun x => matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient w x))
      ((volume : Measure R3).restrict ballOpens) := by
    refine (integrable_mbf_test ha.continuous (W1p.gradient u) φ).congr ?_
    filter_upwards [hgw] with x hx
    rw [hx]
  have e0 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
      (gradient (fun y => q y + w y) x) =
      ∫ x in (ballOpens : Set R3), (matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient q x)
        + matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (gradient w x)) := by
    refine setIntegral_congr_fun hB.measurableSet fun x hx => ?_
    have hdq : DifferentiableAt ℝ q x := (hq.differentiable (by simp)) x
    have hdw : DifferentiableAt ℝ w x :=
      (hw.differentiableOn (by simp) x hx).differentiableAt (hB.mem_nhds hx)
    have : gradient (fun y => q y + w y) x = gradient q x + gradient w x := by
      simp only [gradient, fderiv_fun_add hdq hdw, map_add]
    rw [this, map_add]
  rw [e0, integral_add iq iw]
  have e1 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
      (gradient q x) = -∫ x in (ballOpens : Set R3), F x * φ x := by
    rw [integral_mbf_smooth ha hq.contDiffOn φ]
    congr 1
    refine (setIntegral_congr_fun hB.measurableSet fun x hx => by rw [hqg x hx]).trans ?_
    refine integral_congr_ae ?_
    filter_upwards [hFg] with x hx
    rw [hx]
  have e2 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
      (gradient w x) = ∫ x in (ballOpens : Set R3), F x * φ x := by
    rw [← hu φ]
    refine integral_congr_ae ?_
    filter_upwards [hgw] with x hx
    rw [hx]
  rw [e1, e2]; ring

end OAI.AnisotropicCalderon.Regularity.Jets
