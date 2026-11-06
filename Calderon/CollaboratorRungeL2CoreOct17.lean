import Calderon.CollaboratorAffineSobolevOct17
import Calderon.CollaboratorUniqueContinuationDefinitionOct17

/-! Helpers for the `L²` Runge approximation `l2_runge` (Lassas–Liimatainen–Salo Prop. A.6). -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.RungeAux
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine
open scoped Matrix

/-- Matrices are pseudo-metrizable (instance search does not see through `Matrix`). -/
theorem pseudoMetrizableSpace_matrix :
    PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

attribute [local instance] pseudoMetrizableSpace_matrix

/-! ### Pointwise facts about the coefficients -/

theorem mbf_symm {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) (η ξ : R3) :
    matrixBilinearForm A η ξ = matrixBilinearForm A ξ η := by
  have hT : A.transpose = A := by
    have := hA.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [← matrixBilinearForm_transpose_apply, hT]

theorem uniformlyEllipticOn_closedBall {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Continuous A) (hpos : ∀ x, (A x).PosDef) (c : R3) (R : ℝ) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn (closedBall c R) A lam Lam := by
  -- upper bound
  have hcont : Continuous fun x => ‖matrixBilinearForm (A x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp (continuous_matrixBilinearForm.comp hA)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).bddAbove_image hcont.continuousOn
  have hupper : ∀ x ∈ closedBall c R, ∀ η ξ : R3,
      |η ⬝ᵥ (A x *ᵥ ξ)| ≤ max M 1 * ‖η‖ * ‖ξ‖ := by
    intro x hx η ξ
    have hb : ‖matrixBilinearForm (A x)‖ ≤ max M 1 :=
      (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
    calc |η ⬝ᵥ (A x *ᵥ ξ)| = ‖matrixBilinearForm (A x) η ξ‖ := by
          rw [matrixBilinearForm_apply, Real.norm_eq_abs]
      _ ≤ ‖matrixBilinearForm (A x)‖ * ‖η‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr
  -- lower bound
  let Q : R3 × R3 → ℝ := fun z => z.2 ⬝ᵥ (A z.1 *ᵥ z.2)
  have hvec : Continuous fun z : R3 × R3 => (z.2 : Fin 3 → ℝ) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hQ : Continuous Q :=
    hvec.dotProduct ((hA.comp continuous_fst).matrix_mulVec hvec)
  have hK := (isCompact_closedBall c R).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hlamQ⟩ := hK.exists_forall_le' hQ.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    simpa [Q] using (hpos z.1).dotProduct_mulVec_pos hv)
  refine ⟨lam, max (max M 1) lam, hlam, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨?_, fun η ξ => (hupper x hx η ξ).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg η))
      (norm_nonneg ξ))⟩
  intro ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hs : (‖ξ‖⁻¹ • ξ : R3) ∈ Metric.sphere 0 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hlamQ (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hs⟩
  have hscaled : (A x).toQuadraticForm' (‖ξ‖⁻¹ • ξ) =
      ‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ := by
    simpa [pow_two, smul_eq_mul] using
      (A x).toQuadraticForm'.map_smul ‖ξ‖⁻¹ (ξ : Fin 3 → ℝ)
  have hb' : lam ≤ ‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ := by
    rw [← hscaled]
    simpa only [Q, Matrix.toQuadraticForm'_apply, WithLp.ofLp_smul] using hb
  have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖ξ‖)
  have he : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ) = (A x).toQuadraticForm' ξ := by
    field_simp [hn]
  rw [he] at hm
  simpa only [mul_comm] using hm

/-! ### The Dirichlet problem on a ball -/

section Generic

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

theorem energyFormH1_zero_eq (u v : W1p mu Omega 2) :
    energyFormH1 a 0 0 u v = ∫ x in Omega,
      matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [energyIntegrand_apply]

theorem energyFormH1_zero_sub
    (hcoeff : MemLp (fun x => energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))
    (u w v : W1p mu Omega 2) :
    energyFormH1 a 0 0 (u - w) v = energyFormH1 a 0 0 u v - energyFormH1 a 0 0 w v := by
  rw [← energyFormH1L_apply hcoeff, ← energyFormH1L_apply hcoeff, ← energyFormH1L_apply hcoeff,
    map_sub, sub_apply]

end Generic

section Ball

variable (c : R3) {R : ℝ} (hR : 0 < R) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
  (hA : Continuous A) (hpos : ∀ x, (A x).PosDef)
include hR hA hpos

omit hR in
theorem memLp_coeff :
    MemLp (fun x => energyIntegrand (A x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict (ballO c R)) := by
  obtain ⟨lam, Lam, hu⟩ := uniformlyEllipticOn_closedBall hA hpos c R
  exact memLp_energyIntegrand_of_bounds hu.upper_nonneg hA.aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx eta xi => hu.upper_bound (ball_subset_closedBall hx) eta xi)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

theorem existsUnique_ball (F : Lp ℝ 2 ((volume : Measure R3).restrict (ballO c R))) :
    ∃! u : W1p0 (volume : Measure R3) (ballO c R) 2, IsWeakSolutionDirichlet A 0 0 F u := by
  obtain ⟨lam, Lam, hu⟩ := uniformlyEllipticOn_closedBall hA hpos c R
  exact UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball (n := 2)
    (hu.mono_set ball_subset_closedBall) hA.aestronglyMeasurable aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
    (fun _ _ => le_rfl) hR.le (z := c) subset_rfl (by simpa using hu.1) F

theorem exists_weak (F : Lp ℝ 2 ((volume : Measure R3).restrict (ballO c R))) :
    ∃ w : W1p (volume : Measure R3) (ballO c R) 2,
      w ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 ∧
      ∀ φ : W1p (volume : Measure R3) (ballO c R) 2,
        φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
        ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w x) =
          ∫ x in ball c R, F x * W1p.value φ x := by
  obtain ⟨u, hu, -⟩ := existsUnique_ball c hR hA hpos F
  refine ⟨u.1, u.2, fun φ hφ => ?_⟩
  have h := (isWeakSolutionDirichlet_iff F u).1 hu ⟨φ, hφ⟩
  rw [energyFormH1_zero_eq] at h
  exact h

theorem eq_of_weak {w₁ w₂ : W1p (volume : Measure R3) (ballO c R) 2}
    (h₁ : w₁ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2)
    (h₂ : w₂ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2)
    (h : ∀ φ : W1p (volume : Measure R3) (ballO c R) 2,
        φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
        ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w₁ x) =
          ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient w₂ x)) :
    w₁ = w₂ := by
  have hcoeff := memLp_coeff c hA hpos (R := R)
  have hsol : ∀ u : W1p0 (volume : Measure R3) (ballO c R) 2,
      (∀ φ : W1p0 (volume : Measure R3) (ballO c R) 2,
        energyFormH1 A 0 0 (u : W1p (volume : Measure R3) (ballO c R) 2)
          (φ : W1p (volume : Measure R3) (ballO c R) 2) = 0) →
      IsWeakSolutionDirichlet A 0 0 (0 : Lp ℝ 2 ((volume : Measure R3).restrict (ballO c R))) u := by
    intro u hu
    refine (isWeakSolutionDirichlet_iff _ u).2 fun φ => ?_
    rw [hu φ]
    refine (integral_eq_zero_of_ae ?_).symm
    filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict (ballO c R))] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  obtain ⟨u0, -, huniq⟩ := existsUnique_ball c hR hA hpos 0
  have hd := huniq ⟨w₁ - w₂, sub_mem h₁ h₂⟩ (hsol _ fun φ => by
    rw [energyFormH1_zero_sub hcoeff, energyFormH1_zero_eq, energyFormH1_zero_eq]
    exact sub_eq_zero.2 (h φ φ.2))
  have hz := huniq 0 (hsol _ fun φ => by
    rw [← energyFormH1L_apply hcoeff]
    simp)
  have := congrArg Subtype.val (hd.trans hz.symm)
  simpa [sub_eq_zero] using this

end Ball

end OAI.AnisotropicCalderon.Regularity.RungeAux
