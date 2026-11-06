import Calderon.CollaboratorBallRegularityOct17
import TauCeti.Analysis.PDE.Caccioppoli.Basic

/-! Interior estimates: `W^{k,2}` norms on a smaller concentric ball bounded by the `L²` norm
(helper for task 08).

The proof pulls the solution back to the unit ball and bootstraps: with nested cutoffs
`ζ_N` (`ζ_N = 1` near `tsupport ζ_{N+1}`), the product `ζ_{N+1} w ∈ H¹₀(B)` solves a Dirichlet
problem whose forcing is a first-order expression in `ζ_N w`, so `ball_regularity_bound` gains
one derivative at each step.  The base case is the Caccioppoli inequality. -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ContDiff Matrix.Norms.Elementwise Distributions Gradient
namespace OAI.AnisotropicCalderon.Regularity.IntEst
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine EnergyBridge

/-- Weak solutions of `div(a ∇w) = 0` on the unit ball, tested against test functions. -/
def Sol (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (w : W1p (volume : Measure R3) ballOpens 2) : Prop :=
  ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
    matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x) = 0

/-- The `H^{N+1}` estimate for the cutoff `ζ w` of solutions, by the `L²` norm of `w`. -/
def Est (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (ζ : R3 → ℝ) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : W1p (volume : Measure R3) ballOpens 2, Sol a w →
    ∃ U : Wkp (volume : Measure R3) ballOpens 2 (N + 1),
      (⇑(Wkp.value (N + 1) U) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ζ x * W1p.value w x) ∧ ‖U‖ ≤ C * ‖W1p.value w‖

theorem gradient_eq_zero_of_eqOn {ζ : R3 → ℝ} {O : Set R3} (hO : IsOpen O)
    (h1 : ∀ y ∈ O, ζ y = 1) {x : R3} (hx : x ∈ O) : gradient ζ x = 0 := by
  have h : ζ =ᶠ[nhds x] fun _ => (1 : ℝ) := Filter.eventually_of_mem (hO.mem_nhds hx) h1
  simp [gradient, h.fderiv_eq]

theorem div_eq_zero_of_notMem {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) {x : R3} (hx : x ∉ tsupport ψ) :
    divCoeffGradient a ψ x = 0 := by
  unfold divCoeffGradient
  refine Finset.sum_eq_zero fun i _ => ?_
  have hg : ContDiff ℝ ∞ (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (gradient ψ y)) := by
    have : (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (gradient ψ y)) = fun y => ∑ i', ∑ k, (EuclideanSpace.basisFun (Fin 3) ℝ i) i' *
          a y i' k * gradient ψ y k := funext fun y => HO.matrixBilinearForm_eq_sum _ _ _
    rw [this]
    exact ContDiff.sum fun i' _ => ContDiff.sum fun k _ =>
      (contDiff_const.mul (HO.contDiff_matrix_entry ha i' k)).mul (HO.contDiff_gradient_coord hψ k)
  have hsub : tsupport (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (gradient ψ y)) ⊆ tsupport ψ :=
    closure_minimal (fun y hy => by_contra fun hyψ => hy (by
      simp [HO.gradient_eq_zero_of_notMem_tsupport hyψ])) (isClosed_tsupport ψ)
  have hxi : x ∉ tsupport (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (gradient ψ y)) := fun h => hx (hsub h)
  rw [(hg.differentiable (by simp) x).lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hxi]
  simp

theorem locForcing_eq_neg_sum {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {ζ : R3 → ℝ}
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (u : W1p (volume : Measure R3) ballOpens 2) (x : R3) (hf : f x = 0) :
    locForcing a ζ f u x = -((∑ k, (a x 0 k + a x k 0) * gradient ζ x k) *
        W1p.gradient u x 0 + (∑ k, (a x 1 k + a x k 1) * gradient ζ x k) *
        W1p.gradient u x 1 + (∑ k, (a x 2 k + a x k 2) * gradient ζ x k) *
        W1p.gradient u x 2 + divCoeffGradient a ζ x * W1p.value u x) := by
  simp only [locForcing, hf, HO.matrixBilinearForm_eq_sum, Fin.sum_univ_three]
  ring

/-- The localized forcing as a bounded operator `H^{N+1} → H^N`. -/
theorem exists_forcingOp {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {ζ : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (N : ℕ) :
    ∃ L : Wkp (volume : Measure R3) ballOpens 2 (N + 1) →L[ℝ]
        Wkp (volume : Measure R3) ballOpens 2 N,
      ∀ U, ⇑(Wkp.value N (L U)) =ᵐ[(volume : Measure R3).restrict ballOpens]
        locForcing a ζ (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
          (Wkp.firstOrder N U) := by
  let b : Fin 3 → R3 → ℝ := fun i x => ∑ k, (a x i k + a x k i) * gradient ζ x k
  have hb : ∀ i, ContDiff ℝ ∞ (b i) := fun i => ContDiff.sum fun k _ =>
    ((HO.contDiff_matrix_entry ha i k).add (HO.contDiff_matrix_entry ha k i)).mul
      (HO.contDiff_gradient_coord hζ k)
  have hbc : ∀ i, HasCompactSupport (b i) := fun i =>
    hζc.mono' fun x hx => by_contra fun h => hx (by
      simp [b, HO.gradient_eq_zero_of_notMem_tsupport h])
  have hD := HO.contDiff_divCoeffGradient ha hζ
  have hDc : HasCompactSupport (divCoeffGradient a ζ) :=
    hζc.mono' fun x hx => by_contra fun h => hx (div_eq_zero_of_notMem ha hζ h)
  obtain ⟨Cm, -, hm⟩ := DirichletFamily.mulAt (Ω := ballOpens) N
  have hT : ∀ φ : R3 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∃ T : Wkp (volume : Measure R3) ballOpens 2 N →L[ℝ] Wkp (volume : Measure R3) ballOpens 2 N,
        ∀ f, ⇑(Wkp.value N (T f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
          fun x => φ x * Wkp.value N f x := fun φ hφ hφc => by
    obtain ⟨M, hM, hbd⟩ := HO.exists_iteratedFDeriv_bound hφ hφc (N + 1)
    obtain ⟨T, hT, -⟩ := hm φ hφ hφc M hM hbd
    exact ⟨T, hT⟩
  choose Tb hTb using fun i => hT (b i) (hb i) (hbc i)
  obtain ⟨TD, hTD⟩ := hT _ hD hDc
  refine ⟨-((Tb 0).comp (WkpCalculus.dL 0 N) + (Tb 1).comp (WkpCalculus.dL 1 N) +
    (Tb 2).comp (WkpCalculus.dL 2 N) + TD.comp (Wkp.lowerOrderL N)), fun U => ?_⟩
  have hv : Wkp.value N ((-((Tb 0).comp (WkpCalculus.dL 0 N) + (Tb 1).comp (WkpCalculus.dL 1 N) +
      (Tb 2).comp (WkpCalculus.dL 2 N) + TD.comp (Wkp.lowerOrderL N))) U) =
      -(Wkp.value N (Tb 0 (WkpCalculus.dL 0 N U)) + Wkp.value N (Tb 1 (WkpCalculus.dL 1 N U)) +
        Wkp.value N (Tb 2 (WkpCalculus.dL 2 N U)) + Wkp.value N (TD (Wkp.lowerOrderL N U))) := by
    simp only [← Wkp.valueL_apply, map_neg, map_add, _root_.neg_apply,
      _root_.add_apply, ContinuousLinearMap.comp_apply]
  have hlow : Wkp.value N (Wkp.lowerOrderL N U) = W1p.value (Wkp.firstOrder N U) := by
    rw [Wkp.lowerOrderL_apply, Wkp.value_firstOrder, Wkp.value_succ]
  rw [hv]
  filter_upwards [Lp.coeFn_neg (Wkp.value N (Tb 0 (WkpCalculus.dL 0 N U)) +
      Wkp.value N (Tb 1 (WkpCalculus.dL 1 N U)) + Wkp.value N (Tb 2 (WkpCalculus.dL 2 N U)) +
      Wkp.value N (TD (Wkp.lowerOrderL N U))),
    Lp.coeFn_add (Wkp.value N (Tb 0 (WkpCalculus.dL 0 N U)) +
      Wkp.value N (Tb 1 (WkpCalculus.dL 1 N U)) + Wkp.value N (Tb 2 (WkpCalculus.dL 2 N U)))
      (Wkp.value N (TD (Wkp.lowerOrderL N U))),
    Lp.coeFn_add (Wkp.value N (Tb 0 (WkpCalculus.dL 0 N U)) +
      Wkp.value N (Tb 1 (WkpCalculus.dL 1 N U))) (Wkp.value N (Tb 2 (WkpCalculus.dL 2 N U))),
    Lp.coeFn_add (Wkp.value N (Tb 0 (WkpCalculus.dL 0 N U)))
      (Wkp.value N (Tb 1 (WkpCalculus.dL 1 N U))),
    hTb 0 (WkpCalculus.dL 0 N U), hTb 1 (WkpCalculus.dL 1 N U), hTb 2 (WkpCalculus.dL 2 N U),
    hTD (Wkp.lowerOrderL N U), WkpCalculus.value_d 0 N U, WkpCalculus.value_d 1 N U,
    WkpCalculus.value_d 2 N U,
    Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h0
  rw [locForcing_eq_neg_sum _ x h0, h1, Pi.neg_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4,
    Pi.add_apply, h5, h6, h7, h8, WkpCalculus.dL_apply, WkpCalculus.dL_apply,
    WkpCalculus.dL_apply, h9, h10, h11, hlow]

theorem sol_zero {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {w : W1p (volume : Measure R3) ballOpens 2}
    (hw : Sol a w) (φ : 𝓓(ballOpens, ℝ)) : ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x) =
        ∫ x in (ballOpens : Set R3),
          (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x * φ x := by
  rw [hw φ]
  refine (integral_eq_zero_of_ae ?_).symm
  filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
  rw [hx]; simp

/-- The Caccioppoli base case. -/
theorem est_zero {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    (hpos : ∀ x, (a x).PosDef) {ζ : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ (ballOpens : Set R3)) : Est a ζ 0 := by
  obtain ⟨lam, Lam, hell⟩ := BallReg.exists_uniformlyEllipticOn ha.continuous hpos
  obtain ⟨M, hM, hζM, hgM⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  have hK0 : 0 ≤ (2 * Lam / lam) ^ 2 := sq_nonneg _
  refine ⟨M * (2 * (2 * Lam / lam) ^ 2 + 3), by positivity, fun w hw => ?_⟩
  have htest := sol_zero hw
  have hu : ∀ v : W1p0 (volume : Measure R3) ballOpens 2,
      energyFormH1 a 0 0 w (v : W1p (volume : Measure R3) ballOpens 2) =
        ∫ x in (ballOpens : Set R3),
          (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x *
            W1p.value (v : W1p (volume : Measure R3) ballOpens 2) x := by
    intro v
    rw [energyFormH1_def, ← eq_of_testFunction ha.continuous htest _ v.2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [energyIntegrand_apply]
  have hc := UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le hell
    ha.continuous.aestronglyMeasurable hu hζ hζc hts
  have hz : ∫ x in (ballOpens : Set R3), ζ x ^ 2 *
      (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x * W1p.value w x = 0 :=
    integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
      rw [hx]; simp)
  rw [hz, mul_zero, add_zero] at hc
  have hI2 : ∫ x in (ballOpens : Set R3), ‖gradient ζ x‖ ^ 2 * W1p.value w x ^ 2 ≤
      M ^ 2 * ‖W1p.value w‖ ^ 2 := by
    rw [← W1p.integral_value_sq_eq_norm_value_sq, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((W1p.integrable_value_sq w).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hgM x) 2) (sq_nonneg _)
  have hζM' : ∀ x ∈ ballOpens, |ζ x| ≤ M := fun x _ => hζM x
  have hgM' : ∀ x ∈ ballOpens, ‖gradient ζ x‖ ≤ M := fun x _ => hgM x
  have hgrad := W1p.norm_gradient_contDiffSMul_sq_le hζ hM hζM' hgM' w
  have hval : ‖W1p.value (W1p.contDiffSMul ζ hζ hM hζM' hgM' w)‖ ≤ M * ‖W1p.value w‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [W1p.value_contDiffSMul_ae hζ hM hζM' hgM' w] with x hx
    rw [hx, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hζM x) (norm_nonneg _)
  refine ⟨(W1p.contDiffSMul ζ hζ hM hζM' hgM' w : Wkp (volume : Measure R3) ballOpens 2 1),
    ?_, ?_⟩
  · have e : Wkp.value 1 (W1p.contDiffSMul ζ hζ hM hζM' hgM' w) =
        W1p.value (W1p.contDiffSMul ζ hζ hM hζM' hgM' w) := Wkp.value_one _
    rw [e]
    filter_upwards [W1p.value_contDiffSMul_ae hζ hM hζM' hgM' w] with x hx
    rw [hx, smul_eq_mul]
  · have hv2 := pow_le_pow_left₀ (norm_nonneg _) hval 2
    rw [mul_pow] at hv2
    have hn := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq
      (W1p.contDiffSMul ζ hζ hM hζM' hgM' w)
    set t := M ^ 2 * ‖W1p.value w‖ ^ 2 with ht
    have ht0 : 0 ≤ t := by positivity
    set K := (2 * Lam / lam) ^ 2 with hK
    have hI1 := hc.trans (mul_le_mul_of_nonneg_left hI2 hK0)
    have hsq : ‖(W1p.contDiffSMul ζ hζ hM hζM' hgM' w : W1p (volume : Measure R3) ballOpens 2)‖ ^ 2
        ≤ (M * (2 * K + 3) * ‖W1p.value w‖) ^ 2 := by
      have e2 : (M * (2 * K + 3) * ‖W1p.value w‖) ^ 2 = t * (2 * K + 3) ^ 2 := by
        rw [ht]; ring
      rw [hn, e2]
      have h3 : t * (2 * K + 3) ≤ t * (2 * K + 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) ht0
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- The bootstrap step. -/
theorem est_succ {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    (hpos : ∀ x, (a x).PosDef) {ζ ζ' : R3 → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ (ballOpens : Set R3)) {O : Set R3} (hO : IsOpen O)
    (hζO : tsupport ζ ⊆ O) (hζ' : ContDiff ℝ ∞ ζ') (hζ'c : HasCompactSupport ζ')
    (h1 : ∀ x ∈ O, ζ' x = 1) (N : ℕ) (ih : Est a ζ' N) : Est a ζ (N + 1) := by
  obtain ⟨C', hC', hih⟩ := ih
  obtain ⟨L, hL⟩ := exists_forcingOp ha hζ hζc N
  obtain ⟨Cr, hCr, hreg0⟩ := ball_regularity_bound 0 one_pos ha hpos N
  have hreg : ∀ (G : Wkp (volume : Measure R3) ballOpens 2 N)
      (w : W1p (volume : Measure R3) ballOpens 2),
      w ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      (∀ φ : W1p (volume : Measure R3) ballOpens 2,
        φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x)
          (W1p.gradient w x) = ∫ x in (ballOpens : Set R3), Wkp.value N G x * W1p.value φ x) →
      ∃ W : Wkp (volume : Measure R3) ballOpens 2 (N + 1 + 1),
        Wkp.firstOrder (N + 1) W = w ∧ ‖W‖ ≤ Cr * (‖w‖ + ‖G‖) := hreg0
  obtain ⟨M, hM, hζM, hgM⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  obtain ⟨M', hM', hζM', hgM'⟩ := (hζ'.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζ'c
  have hζMb : ∀ x ∈ ballOpens, |ζ x| ≤ M := fun x _ => hζM x
  have hgMb : ∀ x ∈ ballOpens, ‖gradient ζ x‖ ≤ M := fun x _ => hgM x
  have hζMb' : ∀ x ∈ ballOpens, |ζ' x| ≤ M' := fun x _ => hζM' x
  have hgMb' : ∀ x ∈ ballOpens, ‖gradient ζ' x‖ ≤ M' := fun x _ => hgM' x
  refine ⟨Cr * (2 * M + ‖L‖) * C', by positivity, fun w hw => ?_⟩
  obtain ⟨U', hU'v, hU'n⟩ := hih w hw
  have hfo : Wkp.firstOrder N U' = W1p.contDiffSMul ζ' hζ' hM' hζMb' hgMb' w := by
    apply W1p.ext_value
    apply Lp.ext
    rw [Wkp.value_firstOrder]
    filter_upwards [hU'v, W1p.value_contDiffSMul_ae hζ' hM' hζMb' hgMb' w] with x e1 e2
    rw [e1, e2, smul_eq_mul]
  obtain ⟨V, hVdef⟩ : ∃ V, V = W1p.contDiffSMul ζ hζ hM hζMb hgMb w := ⟨_, rfl⟩
  have hV0 : V ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    rw [hVdef]
    exact W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hζ hM hζMb hgMb
      hζc hts w
  have hVeq : V = W1p.contDiffSMul ζ hζ hM hζMb hgMb (Wkp.firstOrder N U') := by
    rw [hVdef]
    apply W1p.ext_value
    apply Lp.ext
    filter_upwards [W1p.value_contDiffSMul_ae hζ hM hζMb hgMb w,
      W1p.value_contDiffSMul_ae hζ hM hζMb hgMb (Wkp.firstOrder N U'), hU'v] with x e1 e2 e3
    rw [e1, e2, Wkp.value_firstOrder, e3, smul_eq_mul, smul_eq_mul]
    by_cases hx : ζ x = 0
    · simp [hx]
    · rw [h1 x (hζO (subset_tsupport _ hx)), one_mul]
  have hVn : ‖V‖ ≤ 2 * M * ‖U'‖ := by
    rw [hVeq]
    exact (W1p.norm_contDiffSMul_le hζ hM hζMb hgMb _).trans
      (mul_le_mul_of_nonneg_left (DirichletFamily.norm_firstOrder_le N U') (by positivity))
  have hgfo : ⇑(W1p.gradient (Wkp.firstOrder N U')) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => ζ' x • W1p.gradient w x + W1p.value w x • gradient ζ' x := by
    rw [hfo]; exact W1p.gradient_contDiffSMul_ae hζ' hM' hζMb' hgMb' w
  have hvfo : ⇑(W1p.value (Wkp.firstOrder N U')) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => ζ' x * W1p.value w x := by
    rw [Wkp.value_firstOrder]; exact hU'v
  have hloc : locForcing a ζ (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
      (Wkp.firstOrder N U') =ᵐ[(volume : Measure R3).restrict ballOpens]
      locForcing a ζ (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) w := by
    filter_upwards [hgfo, hvfo] with x e1 e2
    by_cases hx : x ∈ O
    · simp only [locForcing, e1, e2, h1 x hx, gradient_eq_zero_of_eqOn hO h1 hx, one_smul,
        smul_zero, add_zero, one_mul]
    · have hxt : x ∉ tsupport ζ := fun h => hx (hζO h)
      simp only [locForcing, image_eq_zero_of_notMem_tsupport hxt,
        HO.gradient_eq_zero_of_notMem_tsupport hxt, div_eq_zero_of_notMem ha hζ hxt, map_zero,
        zero_mul, mul_zero, sub_zero, _root_.zero_apply]
  obtain ⟨F, hF, hFeq⟩ := exists_localized_forcing_eq ha (sol_zero hw) hζ
  have hFL : F = Wkp.value N (L U') := Lp.ext (hF.trans (hloc.symm.trans (hL U').symm))
  have htest : ∀ φ : 𝓓(ballOpens, ℝ), ∫ x in (ballOpens : Set R3),
      matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W1p.gradient V x) =
        ∫ x in (ballOpens : Set R3), Wkp.value N (L U') x * φ x := by
    intro φ
    rw [← hFL, ← hFeq φ, hVdef]
    refine integral_congr_ae ?_
    filter_upwards [W1p.gradient_contDiffSMul_ae hζ hM hζMb hgMb w] with x hx
    rw [hx]
  obtain ⟨U, hUfo, hUn⟩ := hreg (L U') V hV0
    (fun φ hφ => eq_of_testFunction ha.continuous htest φ hφ)
  refine ⟨U, ?_, ?_⟩
  · have e : ⇑(W1p.value V) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ζ x * W1p.value w x := by
      rw [hVdef]
      filter_upwards [W1p.value_contDiffSMul_ae hζ hM hζMb hgMb w] with x hx
      rw [hx, smul_eq_mul]
    have e2 : Wkp.value (N + 1 + 1) U = W1p.value V :=
      (Wkp.value_firstOrder (N + 1) U).symm.trans (congrArg W1p.value hUfo)
    rw [e2]
    exact e
  · calc ‖U‖ ≤ Cr * (‖V‖ + ‖L U'‖) := hUn
      _ ≤ Cr * (2 * M * ‖U'‖ + ‖L‖ * ‖U'‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hVn (L.le_opNorm U')) hCr
      _ = Cr * (2 * M + ‖L‖) * ‖U'‖ := by ring
      _ ≤ Cr * (2 * M + ‖L‖) * (C' * ‖W1p.value w‖) :=
          mul_le_mul_of_nonneg_left hU'n (by positivity)
      _ = Cr * (2 * M + ‖L‖) * C' * ‖W1p.value w‖ := by ring

/-- The unit-ball interior estimate. -/
theorem unit_est {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    (hpos : ∀ x, (a x).PosDef) (N : ℕ) : ∀ s : ℝ, 0 < s → s < 1 →
    ∃ ζ : R3 → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ (ballOpens : Set R3) ∧ (∀ x ∈ ball (0 : R3) s, ζ x = 1) ∧ Est a ζ N := by
  induction N with
  | zero =>
    intro s hs0 hs1
    let η : ContDiffBump (0 : R3) := ⟨s, (s + 1) / 2, hs0, by linarith⟩
    have hts : tsupport (η : R3 → ℝ) ⊆ (ballOpens : Set R3) := by
      rw [η.tsupport_eq, coe_ballOpens, B]
      exact closedBall_subset_ball (show (s + 1) / 2 < 1 by linarith)
    exact ⟨η, η.contDiff, η.hasCompactSupport, hts,
      fun x hx => η.one_of_mem_closedBall (ball_subset_closedBall hx),
      est_zero ha hpos η.contDiff η.hasCompactSupport hts⟩
  | succ N ih =>
    intro s hs0 hs1
    obtain ⟨ζ', hζ', hζ'c, -, hζ'1, hest⟩ := ih ((s + 1) / 2) (by linarith) (by linarith)
    let η : ContDiffBump (0 : R3) := ⟨s, (s + (s + 1) / 2) / 2, hs0, by linarith⟩
    have hts' : tsupport (η : R3 → ℝ) ⊆ ball (0 : R3) ((s + 1) / 2) := by
      rw [η.tsupport_eq]
      exact closedBall_subset_ball (show (s + (s + 1) / 2) / 2 < (s + 1) / 2 by linarith)
    have hts : tsupport (η : R3 → ℝ) ⊆ (ballOpens : Set R3) := by
      rw [coe_ballOpens, B]
      exact hts'.trans (ball_subset_ball (by linarith))
    exact ⟨η, η.contDiff, η.hasCompactSupport, hts,
      fun x hx => η.one_of_mem_closedBall (ball_subset_closedBall hx),
      est_succ ha hpos η.contDiff η.hasCompactSupport hts isOpen_ball hts' hζ' hζ'c hζ'1 N hest⟩

/-! ### Affine transport -/

theorem gradient_comp_aff {f : R3 → ℝ} (hf : Differentiable ℝ f) (c : R3) (s : ℝ) (z : R3) :
    ∇ (fun z => f (c + s • z)) z = s • ∇ f (c + s • z) := by
  have hd : HasFDerivAt (fun z => f (c + s • z))
      ((fderiv ℝ f (c + s • z)).comp (s • ContinuousLinearMap.id ℝ R3)) z :=
    (hf _).hasFDerivAt.comp z (((hasFDerivAt_id z).const_smul s).const_add c)
  refine ext_inner_right ℝ fun v => ?_
  rw [real_inner_smul_left]
  simp only [gradient, InnerProductSpace.toDual_symm_apply, hd.fderiv]
  simp

/-- The weak equation pulled back from `ball x ρ` to the unit ball. -/
theorem pull_eq (x : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (W : W1p (volume : Measure R3) (ballO x ρ) 2)
    (heq : ∀ φ : 𝓓(ballO x ρ, ℝ), ∫ z in ball x ρ,
      matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z) (W1p.gradient W z) = 0) :
    Sol (fun y => A (x + ρ • y)) (pullWkp x hρ 1 W : W1p (volume : Measure R3) ballOpens 2) := by
  intro ψ
  let φ : 𝓓(ballO x ρ, ℝ) := compTest (inv_pos.2 hρ) (isAff_symm hρ (isAff_ball x hρ)) ψ
  have hφ : ∀ z, ∇ (φ : R3 → ℝ) z = ρ⁻¹ • ∇ (ψ : R3 → ℝ) (-(ρ⁻¹ • x) + ρ⁻¹ • z) := fun z =>
    gradient_comp_aff (ψ.contDiff.differentiable (by simp)) _ _ z
  let g : R3 → ℝ := fun z =>
    matrixBilinearForm (A z) (gradient (φ : R3 → ℝ) z) (W1p.gradient W z)
  have h0 : ∫ y in ball (0 : R3) 1, g (x + ρ • y) = 0 := by
    have h1 := integral_comp_aff x hρ ((ball x ρ).indicator g)
    rw [integral_indicator measurableSet_ball, heq φ, smul_zero] at h1
    rw [← integral_indicator measurableSet_ball, ← h1]
    congr 1; funext y
    have hy : x + ρ • y ∈ ball x ρ ↔ y ∈ ball (0 : R3) 1 := isAff_ball x hρ y
    by_cases h : y ∈ ball (0 : R3) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hy.2 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hy.1 h'))]
  have hint : ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (x + ρ • y))
      (gradient (ψ : R3 → ℝ) y)
      (W1p.gradient (pullWkp x hρ 1 W : W1p (volume : Measure R3) ballOpens 2) y) =
      ∫ y in ball (0 : R3) 1, ρ ^ 2 * g (x + ρ • y) := by
    refine integral_congr_ae ?_
    filter_upwards [gradient_pullWkp_one x hρ W] with y hy
    rw [hy]
    simp only [g, hφ, aff_symm_aff_zero hρ, map_smul, _root_.smul_apply, smul_eq_mul]
    field_simp
  rw [hint, integral_const_mul, h0, mul_zero]

end OAI.AnisotropicCalderon.Regularity.IntEst

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine EnergyBridge
open IntEst

/-- Interior estimate: weak solutions of `div(A ∇w) = 0` on `ball c r₂` lie in `W^{k,2}` of the
concentric ball `ball c r₁` (`r₁ < r₂`) with norm bounded by the `L²(ball c r₂)` norm. -/
theorem interior_estimate (c : R3) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : W1p (volume : Measure R3) (ballO c r₂) 2,
      (∀ φ : 𝓓(ballO c r₂, ℝ), ∫ x in ball c r₂,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x) = 0) →
      ∃ W : Wkp (volume : Measure R3) (ballO c r₁) 2 k,
        (⇑(Wkp.value k W) =ᵐ[(volume : Measure R3).restrict (ball c r₁)] W1p.value w) ∧
        ‖W‖ ≤ C * ‖W1p.value w‖ := by
  have hR : 0 < r₂ := hr₁.trans hr
  set s : ℝ := r₁ / r₂ with hs
  have hs0 : 0 < s := div_pos hr₁ hR
  have hs1 : s < 1 := (div_lt_one hR).2 hr
  have ha : ContDiff ℝ ∞ (fun y : R3 => A (c + r₂ • y)) :=
    hA.comp (contDiff_const.add (contDiff_const_smul r₂))
  obtain ⟨ζ, -, -, -, hζ1, C, hC, hest⟩ :=
    unit_est ha (fun y => hpos (c + r₂ • y)) k s hs0 hs1
  let P := (pullWkp c hR k).symm.toContinuousLinearMap
  refine ⟨‖P‖ * C * kC r₂, by have := kC_nonneg r₂; positivity, fun w hw => ?_⟩
  have hsol := pull_eq c hR w hw
  obtain ⟨U, hUv, hUn⟩ := hest _ hsol
  have hle : ballO c r₁ ≤ ballO c r₂ := fun x hx => ball_subset_ball hr.le hx
  refine ⟨Wkp.restrictL hle k (P (Wkp.lowerOrder k U)), ?_, ?_⟩
  · have hq := qmp (inv_pos.2 hR) (isAff_symm hR (isAff_ball c hR))
    have hsub : ball c r₁ ⊆ ball c r₂ := ball_subset_ball hr.le
    have h1 := Wkp.value_restrictL_ae hle k (P (Wkp.lowerOrder k U))
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub
      (value_pullWkp_symm c hR k (Wkp.lowerOrder k U))
    have h4 := ae_restrict_of_ae_restrict_of_subset hsub (hq.ae_eq_comp hUv)
    have h5 := ae_restrict_of_ae_restrict_of_subset hsub
      (hq.ae_eq_comp (value_pullWkp c hR 1 w))
    have e1 : Wkp.value 1 (pullWkp c hR 1 w) =
        W1p.value (pullWkp c hR 1 w : W1p (volume : Measure R3) ballOpens 2) :=
      Wkp.value_one _
    have e2 : Wkp.value 1 w = W1p.value w := Wkp.value_one w
    have e3 : Wkp.value k (Wkp.lowerOrder k U) = Wkp.value (k + 1) U := (Wkp.value_succ k U).symm
    rw [e1, e2] at h5
    rw [e3] at h2
    filter_upwards [h1, h2, h4, h5, ae_restrict_mem measurableSet_ball] with x hx1 hx2 hx4 hx5 hx
    have haff : aff (-(r₂⁻¹ • c)) r₂⁻¹ x = r₂⁻¹ • (x - c) := by
      rw [aff_apply, smul_sub, sub_eq_neg_add]
    have hζx : ζ (r₂⁻¹ • (x - c)) = 1 := by
      refine hζ1 _ ?_
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
        hs, div_eq_inv_mul]
      exact mul_lt_mul_of_pos_left (by rw [← dist_eq_norm]; exact hx) (inv_pos.2 hR)
    simp only [Function.comp_apply, haff] at hx4 hx5
    rw [hx1]
    refine hx2.trans ?_
    rw [hx4, hζx, one_mul, hx5]
    congr 1
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    abel
  · have hn1 : ‖W1p.value (pullWkp c hR 1 w : W1p (volume : Measure R3) ballOpens 2)‖ =
        kC r₂ * ‖W1p.value w‖ := by
      have e1 : Wkp.value 1 (pullWkp c hR 1 w) =
          W1p.value (pullWkp c hR 1 w : W1p (volume : Measure R3) ballOpens 2) :=
        Wkp.value_one _
      have e2 : Wkp.value 1 w = W1p.value w := Wkp.value_one w
      rw [← e1, ← e2]
      exact (congrArg norm (value_pullL hR (isAff_ball c hR) 1 w)).trans (norm_compL _ _ _)
    calc ‖Wkp.restrictL hle k (P (Wkp.lowerOrder k U))‖ ≤ ‖P (Wkp.lowerOrder k U)‖ :=
          Wkp.norm_restrictL_le _ _ _
      _ ≤ ‖P‖ * ‖Wkp.lowerOrder k U‖ := P.le_opNorm _
      _ ≤ ‖P‖ * ‖U‖ := mul_le_mul_of_nonneg_left (Wkp.norm_lowerOrder_le k U) (norm_nonneg _)
      _ ≤ ‖P‖ * (C * (kC r₂ * ‖W1p.value w‖)) := by
          rw [← hn1]; exact mul_le_mul_of_nonneg_left hUn (norm_nonneg _)
      _ = ‖P‖ * C * kC r₂ * ‖W1p.value w‖ := by ring

end OAI.AnisotropicCalderon.Regularity
