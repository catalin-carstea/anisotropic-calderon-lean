import Calderon.CollaboratorAffineSobolevOct17
import Calderon.CollaboratorRegularityInductionStepOct17
import Calderon.CollaboratorFixedDirichletRegularityOct17

/-! Dirichlet regularity on an arbitrary ball `ball c ρ` for a smooth positive definite
coefficient, transported from the unit ball (helper for tasks 07–09). -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.BallReg
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine EnergyBridge
open Matrix

/-! ### Uniform ellipticity by compactness -/

theorem exists_upper_bound {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ x ∈ closedBall (0 : R3) 1,
      ∀ η ξ : R3, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Λ * ‖η‖ * ‖ξ‖ := by
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (a x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp ha)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hcont.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx η ξ
  have hb : ‖TauCeti.PDE.matrixBilinearForm (a x)‖ ≤ max M 1 :=
    (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  calc
    |η ⬝ᵥ (a x *ᵥ ξ)| = ‖TauCeti.PDE.matrixBilinearForm (a x) η ξ‖ := by
      rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs]
    _ ≤ ‖TauCeti.PDE.matrixBilinearForm (a x)‖ * ‖η‖ * ‖ξ‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr

theorem exists_lower_bound {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a)
    (hpos : ∀ x, (a x).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ closedBall (0 : R3) 1,
      ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ := by
  let Q : R3 × R3 → ℝ := fun z => z.2 ⬝ᵥ (a z.1 *ᵥ z.2)
  have hvec : Continuous fun z : R3 × R3 => (z.2 : Fin 3 → ℝ) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hQ : Continuous Q :=
    hvec.dotProduct ((ha.comp continuous_fst).matrix_mulVec hvec)
  have hK := (isCompact_closedBall (0 : R3) 1).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hlamQ⟩ := hK.exists_forall_le' hQ.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    simpa [Q] using (hpos z.1).dotProduct_mulVec_pos hv)
  refine ⟨lam, hlam, ?_⟩
  intro x hx ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hs : (‖ξ‖⁻¹ • ξ : R3) ∈ Metric.sphere 0 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hlamQ (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hs⟩
  have hscaled : (a x).toQuadraticForm' (‖ξ‖⁻¹ • ξ) =
      ‖ξ‖⁻¹ ^ 2 * (a x).toQuadraticForm' ξ := by
    simpa [pow_two, smul_eq_mul] using
      (a x).toQuadraticForm'.map_smul ‖ξ‖⁻¹ (ξ : Fin 3 → ℝ)
  have hb' : lam ≤ ‖ξ‖⁻¹ ^ 2 * (a x).toQuadraticForm' ξ := by
    rw [← hscaled]
    simpa only [Q, Matrix.toQuadraticForm'_apply, WithLp.ofLp_smul] using hb
  have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖ξ‖)
  have he : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ ^ 2 * (a x).toQuadraticForm' ξ) =
      (a x).toQuadraticForm' ξ := by
    field_simp [hn]
  rw [he] at hm
  simpa only [mul_comm] using hm

theorem exists_uniformlyEllipticOn {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : Continuous a)
    (hpos : ∀ x, (a x).PosDef) :
    ∃ lam Λ : ℝ, UniformlyEllipticOn (ballOpens : Set R3) a lam Λ := by
  obtain ⟨lam, hlam, hlower⟩ := exists_lower_bound ha hpos
  obtain ⟨M, hM, hupper⟩ := exists_upper_bound ha
  have hsub : (ballOpens : Set R3) ⊆ closedBall 0 1 := by
    rw [coe_ballOpens, B]; exact ball_subset_closedBall
  refine ⟨lam, max M lam, hlam, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨hlower x (hsub hx), ?_⟩
  intro η ξ
  exact (hupper x (hsub hx) η ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left M lam) (norm_nonneg η)) (norm_nonneg ξ))

theorem exists_upper_bound_ball (c : R3) {ρ : ℝ} {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Continuous A) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ x ∈ closedBall c ρ,
      ∀ η ξ : R3, |η ⬝ᵥ (A x *ᵥ ξ)| ≤ Λ * ‖η‖ * ‖ξ‖ := by
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (A x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp hA)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c ρ).bddAbove_image hcont.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx η ξ
  have hb : ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ max M 1 :=
    (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  calc
    |η ⬝ᵥ (A x *ᵥ ξ)| = ‖TauCeti.PDE.matrixBilinearForm (A x) η ξ‖ := by
      rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs]
    _ ≤ ‖TauCeti.PDE.matrixBilinearForm (A x)‖ * ‖η‖ * ‖ξ‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr

/-! ### Change of variables -/

theorem setIntegral_comp {ρ : ℝ} (c : R3) (hρ : 0 < ρ) (g : R3 → ℝ) :
    ∫ y in (ballOpens : Set R3), g (c + ρ • y) = (sc ρ).toReal⁻¹ * ∫ x in ball c ρ, g x := by
  rw [← integral_indicator ballOpens.isOpen.measurableSet,
    ← integral_indicator isOpen_ball.measurableSet]
  have : (ballOpens : Set R3).indicator (fun y => g (c + ρ • y)) =
      fun y => (ball c ρ).indicator g (c + ρ • y) := by
    funext y
    by_cases hy : y ∈ (ballOpens : Set R3)
    · have : c + ρ • y ∈ ball c ρ := (isAff_ball c hρ y).2 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : c + ρ • y ∉ ball c ρ := fun h => hy ((isAff_ball c hρ y).1 h)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [this, integral_comp_aff c hρ, smul_eq_mul]

/-- The pullback commutes with forgetting derivatives. -/
theorem pullWkp_firstOrder (c : R3) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ)
    (W : Wkp (volume : Measure R3) (ballO c ρ) 2 (k + 1)) :
    (pullWkp c hρ 1 (Wkp.firstOrder k W) : W1p (volume : Measure R3) ballOpens 2) =
      Wkp.firstOrder k (pullWkp c hρ (k + 1) W) := by
  apply W1p.ext_value
  apply Lp.ext
  have h1 := value_pullWkp c hρ 1 (Wkp.firstOrder k W)
  have h2 := value_pullWkp c hρ (k + 1) W
  rw [Wkp.value_one] at h1
  rw [Wkp.value_firstOrder]
  refine h1.trans (h2.trans ?_).symm
  refine Filter.Eventually.of_forall fun y => ?_
  show Wkp.value (k + 1) W (c + ρ • y) = W1p.value (Wkp.firstOrder k W) (c + ρ • y)
  rw [Wkp.value_firstOrder]

/-- The transported equation on the unit ball. -/
theorem transported_eq (c : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (m : ℕ) (G : Wkp (volume : Measure R3) (ballO c ρ) 2 m)
    (w : W1p (volume : Measure R3) (ballO c ρ) 2)
    (heq : ∀ φ : W1p (volume : Measure R3) (ballO c ρ) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 →
      ∫ x in ball c ρ, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in ball c ρ, Wkp.value m G x * W1p.value φ x)
    (φ : W1p (volume : Measure R3) (ballO c ρ) 2)
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2) :
    ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (c + ρ • y))
        (W1p.gradient (pullWkp c hρ 1 φ : W1p (volume : Measure R3) ballOpens 2) y)
        (W1p.gradient (pullWkp c hρ 1 w : W1p (volume : Measure R3) ballOpens 2) y) =
      ∫ y in (ballOpens : Set R3), (ρ ^ 2 • Wkp.value m (pullWkp c hρ m G)) y *
        W1p.value (pullWkp c hρ 1 φ : W1p (volume : Measure R3) ballOpens 2) y := by
  have hg1 := gradient_pullWkp_one c hρ φ
  have hg2 := gradient_pullWkp_one c hρ w
  have hv := value_pullWkp c hρ 1 φ
  have e : Wkp.value 1 φ = W1p.value φ := Wkp.value_one φ
  rw [Wkp.value_one, e] at hv
  have hG := value_pullWkp c hρ m G
  have hL : ∫ y in (ballOpens : Set R3), matrixBilinearForm (A (c + ρ • y))
        (W1p.gradient (pullWkp c hρ 1 φ : W1p (volume : Measure R3) ballOpens 2) y)
        (W1p.gradient (pullWkp c hρ 1 w : W1p (volume : Measure R3) ballOpens 2) y) =
      ∫ y in (ballOpens : Set R3), ρ ^ 2 * matrixBilinearForm (A (c + ρ • y))
        (W1p.gradient φ (c + ρ • y)) (W1p.gradient w (c + ρ • y)) := by
    refine integral_congr_ae ?_
    filter_upwards [hg1, hg2] with y h1 h2
    rw [h1, h2]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    ring
  have hR : ∫ y in (ballOpens : Set R3), (ρ ^ 2 • Wkp.value m (pullWkp c hρ m G)) y *
        W1p.value (pullWkp c hρ 1 φ : W1p (volume : Measure R3) ballOpens 2) y =
      ∫ y in (ballOpens : Set R3), ρ ^ 2 *
        (Wkp.value m G (c + ρ • y) * W1p.value φ (c + ρ • y)) := by
    refine integral_congr_ae ?_
    filter_upwards [hv, hG, Lp.coeFn_smul (ρ ^ 2) (Wkp.value m (pullWkp c hρ m G))]
      with y h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
    ring
  rw [hL, hR, integral_const_mul, integral_const_mul,
    setIntegral_comp c hρ (fun x => matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x)),
    setIntegral_comp c hρ (fun x => Wkp.value m G x * W1p.value φ x), heq φ hφ]

end OAI.AnisotropicCalderon.Regularity.BallReg

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine EnergyBridge
open BallReg

/-- `H^{m+2}` regularity on `ball c ρ` of `H¹₀` weak solutions with `H^m` forcing. -/
theorem ball_regularity (c : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) (m : ℕ)
    (G : Wkp (volume : Measure R3) (ballO c ρ) 2 m) (w : W1p (volume : Measure R3) (ballO c ρ) 2)
    (hw0 : w ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2)
    (heq : ∀ φ : W1p (volume : Measure R3) (ballO c ρ) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 →
      ∫ x in ball c ρ, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in ball c ρ, Wkp.value m G x * W1p.value φ x) :
    ∃ W : Wkp (volume : Measure R3) (ballO c ρ) 2 (m + 2), Wkp.firstOrder (m + 1) W = w := by
  let a : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => A (c + ρ • y)
  have ha : ContDiff ℝ ∞ a := hA.comp (contDiff_const.add (contDiff_const_smul ρ))
  obtain ⟨lam, Lam, hell⟩ := exists_uniformlyEllipticOn ha.continuous (fun y => hpos (c + ρ • y))
  have hreg : ∀ n, HO.RegAt a n := fun n =>
    Nat.rec (HO.regAt_zero ha.contDiffOn hell)
      (fun n ih => HO.regAt_succ ha.contDiffOn hell n ih) n
  have hw0' := (pullWkp_one_mem_w1p0_iff c hρ w).2 hw0
  have hH := hreg m (ρ ^ 2 • Wkp.value m (pullWkp c hρ m G))
    ((HO.Hs m).smul_mem _ (HO.mem_Hs.mpr ⟨_, rfl⟩))
    (pullWkp c hρ 1 w : W1p (volume : Measure R3) ballOpens 2) hw0' (fun φ' hφ' => by
      have hs : (pullWkp c hρ 1 ((pullWkp c hρ 1).symm φ') : W1p (volume : Measure R3) ballOpens 2)
          = φ' := (pullWkp c hρ 1).apply_symm_apply φ'
      have hφ : ((pullWkp c hρ 1).symm φ' : W1p (volume : Measure R3) (ballO c ρ) 2) ∈
          w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 := by
        refine (pullWkp_one_mem_w1p0_iff c hρ ((pullWkp c hρ 1).symm φ')).1 ?_
        rw [hs]; exact hφ'
      have := transported_eq c hρ m G w heq _ hφ
      rw [hs] at this
      exact this)
  obtain ⟨W', hW'⟩ := HO.exists_of_value_mem_Hs (m + 1) _ hH
  refine ⟨(pullWkp c hρ (m + 2)).symm W', ?_⟩
  apply (pullWkp c hρ 1).injective
  rw [pullWkp_firstOrder c hρ (m + 1), ContinuousLinearEquiv.apply_symm_apply, hW']

open Matrix in
theorem memLp_coeff_ball (c : R3) {ρ : ℝ} {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Continuous A) {L : ℝ} (hL : 0 ≤ L)
    (hbd : ∀ x ∈ closedBall c ρ, ∀ η ξ : R3, |η ⬝ᵥ (A x *ᵥ ξ)| ≤ L * ‖η‖ * ‖ξ‖) :
    MemLp (fun x => energyIntegrand (A x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict (ballO c ρ)) :=
  memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hL
    (show @Continuous R3 (Fin 3 → Fin 3 → ℝ) _ _ A from hA).aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx => hbd x (ball_subset_closedBall hx)) (by simp) (by simp)

theorem reg_energy (c : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) (m : ℕ)
    (hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict (ballO c ρ)))
    (f : Wkp (volume : Measure R3) (ballO c ρ) 2 m) (u : W1p0 (volume : Measure R3) (ballO c ρ) 2)
    (hu : ∀ v : W1p0 (volume : Measure R3) (ballO c ρ) 2, energyFormH1L0 hcoeff u v =
      dirichletForcing (Wkp.value (mu := (volume : Measure R3)) (Omega := ballO c ρ) (p := 2) m f) v) :
    ∃ U : Wkp (volume : Measure R3) (ballO c ρ) 2 (m + 2),
      Wkp.firstOrder (m + 1) U = (u : W1p (volume : Measure R3) (ballO c ρ) 2) :=
  ball_regularity c hρ hA hpos m f _ u.2 fun φ hφ => by
    have h := hu ⟨φ, hφ⟩
    rw [energyFormH1L0_eq_integral, dirichletForcing_apply_eq_setIntegral] at h
    exact h

theorem bound_bridge (c : R3) {ρ : ℝ} {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (m : ℕ)
    (hcoeff : MemLp (fun x => energyIntegrand (A x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict (ballO c ρ))) (C : ℝ)
    (hk : ∀ (f : Wkp (volume : Measure R3) (ballO c ρ) 2 m)
      (u : W1p0 (volume : Measure R3) (ballO c ρ) 2),
      (∀ v : W1p0 (volume : Measure R3) (ballO c ρ) 2, energyFormH1L0 hcoeff u v =
        dirichletForcing (Wkp.value (mu := (volume : Measure R3)) (Omega := ballO c ρ) (p := 2) m f) v) →
      ∃ U : Wkp (volume : Measure R3) (ballO c ρ) 2 (m + 2),
        Wkp.firstOrder (m + 1) U = (u : W1p (volume : Measure R3) (ballO c ρ) 2) ∧
          ‖U‖ ≤ C * (‖u‖ + ‖f‖))
    (G : Wkp (volume : Measure R3) (ballO c ρ) 2 m) (w : W1p (volume : Measure R3) (ballO c ρ) 2)
    (hw0 : w ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2)
    (heq : ∀ φ : W1p (volume : Measure R3) (ballO c ρ) 2,
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 →
      ∫ x in ball c ρ, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
        ∫ x in ball c ρ, Wkp.value m G x * W1p.value φ x) :
    ∃ W : Wkp (volume : Measure R3) (ballO c ρ) 2 (m + 2),
      Wkp.firstOrder (m + 1) W = w ∧ ‖W‖ ≤ C * (‖w‖ + ‖G‖) :=
  hk G ⟨w, hw0⟩ fun v => by
    rw [energyFormH1L0_eq_integral, dirichletForcing_apply_eq_setIntegral]
    exact heq _ v.2

/-- The quantitative form: one constant for all forcings and solutions. -/
theorem ball_regularity_bound (c : R3) {ρ : ℝ} (hρ : 0 < ρ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Wkp (volume : Measure R3) (ballO c ρ) 2 m)
      (w : W1p (volume : Measure R3) (ballO c ρ) 2),
      w ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 →
      (∀ φ : W1p (volume : Measure R3) (ballO c ρ) 2,
        φ ∈ w1p0Submodule (volume : Measure R3) (ballO c ρ) 2 →
        ∫ x in ball c ρ, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
          ∫ x in ball c ρ, Wkp.value m G x * W1p.value φ x) →
      ∃ W : Wkp (volume : Measure R3) (ballO c ρ) 2 (m + 2),
        Wkp.firstOrder (m + 1) W = w ∧ ‖W‖ ≤ C * (‖w‖ + ‖G‖) := by
  obtain ⟨L, hL, hbd⟩ := exists_upper_bound_ball c (ρ := ρ) hA.continuous
  have hcoeff := memLp_coeff_ball c hA.continuous hL.le hbd
  obtain ⟨C, hC, hk⟩ := DirichletFamily.bounded_of_qual (mu := (volume : Measure R3))
    (Omega := ballO c ρ) hcoeff m (reg_energy c hρ hA hpos m hcoeff)
  exact ⟨C, hC, fun G w hw0 heq => bound_bridge c m hcoeff C hk G w hw0 heq⟩

end OAI.AnisotropicCalderon.Regularity
