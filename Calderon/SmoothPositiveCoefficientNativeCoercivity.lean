import Calderon.TauMetricCoercivity

/-! Expanded first in EXPANSION-smooth-positive-coefficient-native-coercivity-v001.json.
Derive actual native ellipticity/coercivity without exterior normalization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Set
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))

theorem exists_continuousCoefficient_upper_bound (A : MatrixField)
    (hA : Continuous A) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ x ∈ Metric.closedBall (0 : R3) 1,
      ∀ η ξ : R3, |η ⬝ᵥ (A x *ᵥ ξ)| ≤ Λ * ‖η‖ * ‖ξ‖ := by
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (A x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp hA)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hcont.continuousOn
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx η ξ
  have hb : ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ max M 1 :=
    (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
  calc
    |η ⬝ᵥ (A x *ᵥ ξ)| =
        ‖TauCeti.PDE.matrixBilinearForm (A x) η ξ‖ := by
      rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs]
    _ ≤ ‖TauCeti.PDE.matrixBilinearForm (A x)‖ * ‖η‖ * ‖ξ‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr

theorem exists_continuousPositiveCoefficient_lower_bound (A : MatrixField)
    (hA : Continuous A) (hPos : ∀ x, (A x).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ Metric.closedBall (0 : R3) 1,
      ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ (A x).toQuadraticForm' ξ := by
  let Q : R3 × R3 → ℝ := fun z => z.2 ⬝ᵥ (A z.1 *ᵥ z.2)
  have hvec : Continuous fun z : R3 × R3 => (z.2 : Fin 3 → ℝ) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hQ : Continuous Q :=
    hvec.dotProduct ((hA.comp continuous_fst).matrix_mulVec hvec)
  have hK := (isCompact_closedBall (0 : R3) 1).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hlamQ⟩ := hK.exists_forall_le' hQ.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    simpa [Q] using (hPos z.1).dotProduct_mulVec_pos hv)
  refine ⟨lam, hlam, ?_⟩
  intro x hx ξ
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
  have he : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ) =
      (A x).toQuadraticForm' ξ := by
    field_simp [hn]
  rw [he] at hm
  simpa only [mul_comm] using hm


theorem exists_uniformlyEllipticOn_continuousPositiveCoefficient (A : MatrixField)
    (hA : Continuous A) (hPos : ∀ x, (A x).PosDef) :
    ∃ lam Λ : ℝ, TauCeti.PDE.UniformlyEllipticOn (Metric.closedBall (0 : R3) 1)
      (A) lam Λ := by
  obtain ⟨lam, hlam, hlower⟩ := exists_continuousPositiveCoefficient_lower_bound A hA hPos
  obtain ⟨M, hM, hupper⟩ := exists_continuousCoefficient_upper_bound A hA
  refine ⟨lam, max M lam, hlam, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨hlower x hx, ?_⟩
  intro η ξ
  exact (hupper x hx η ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left M lam) (norm_nonneg η)) (norm_nonneg ξ))

/-- The same constants restrict to the exact frozen open ball. -/
theorem exists_uniformlyEllipticOn_continuousPositiveCoefficient_ball (A : MatrixField)
    (hA : Continuous A) (hPos : ∀ x, (A x).PosDef) :
    ∃ lam Λ : ℝ, TauCeti.PDE.UniformlyEllipticOn B (A) lam Λ := by
  obtain ⟨lam, Λ, h⟩ := exists_uniformlyEllipticOn_continuousPositiveCoefficient A hA hPos
  exact ⟨lam, Λ, h.mono_set Metric.ball_subset_closedBall⟩

theorem memLp_continuousCoefficientEnergyIntegrand (A : MatrixField) (hA : Continuous A) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (A x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens) := by
  obtain ⟨M, hM, hupper⟩ := exists_continuousCoefficient_upper_bound A hA
  exact TauCeti.PDE.memLp_energyIntegrand_of_bounds hM.le
    hA.aestronglyMeasurable
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x hx => hupper x (Metric.ball_subset_closedBall hx))
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)


theorem isCoercive_continuousPositiveCoefficientEnergy
    (A : MatrixField) (hA : Continuous A) (hPos : ∀ x, (A x).PosDef)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x) ((0 : R3 → R3) x)
      ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens)) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := A) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff) := by
  obtain ⟨lam, Lam, hu⟩ := exists_uniformlyEllipticOn_continuousPositiveCoefficient_ball A hA hPos
  have hu' : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam := hu
  apply TauCeti.PDE.isCoercive_energyFormH1L0 hcoeff
    (C := (lam ^ 2) / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1)))
  · apply div_pos (sq_pos_of_pos hu.pos)
    have hlam : 0 < lam := hu.pos
    positivity
  · intro w
    have hn : ‖(w : BallH1)‖ = ‖w‖ := rfl
    have hb := hu'.mul_norm_sq_le_energyFormH1_self_of_subset_ball
      hA.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
      (z := 0) (R := 1) (show (ballOpens : Set R3) ⊆ Metric.ball 0 1 from Set.Subset.rfl) w.2
    rw [hn] at hb
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero, mul_one] using hb

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuousCoefficient_upper_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuousPositiveCoefficient_lower_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_uniformlyEllipticOn_continuousPositiveCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_uniformlyEllipticOn_continuousPositiveCoefficient_ball
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_continuousCoefficientEnergyIntegrand
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isCoercive_continuousPositiveCoefficientEnergy
