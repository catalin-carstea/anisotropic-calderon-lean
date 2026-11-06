import Calderon.MetricCoefficient

noncomputable section
open MeasureTheory Matrix

namespace OAI.AnisotropicCalderon.EnergyBridge

/-- Uniform strict positivity on the compact closed ball, obtained from the unit sphere. -/
theorem exists_principalCoefficient_lower_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ Metric.closedBall (0 : R3) 1,
      ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ (principalCoefficient g x).toQuadraticForm' ξ := by
  let Q : R3 × R3 → ℝ := fun z => z.2 ⬝ᵥ (principalCoefficient g z.1 *ᵥ z.2)
  have hvec : Continuous fun z : R3 × R3 => (z.2 : Fin 3 → ℝ) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hQ : Continuous Q :=
    hvec.dotProduct (((continuous_principalCoefficient g hg).comp continuous_fst).matrix_mulVec hvec)
  have hK := (isCompact_closedBall (0 : R3) 1).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hlamQ⟩ := hK.exists_forall_le' hQ.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    simpa [Q] using (principalCoefficient_posDef g hg z.1).dotProduct_mulVec_pos hv)
  refine ⟨lam, hlam, ?_⟩
  intro x hx ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hs : (‖ξ‖⁻¹ • ξ : R3) ∈ Metric.sphere 0 1 := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hlamQ (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hs⟩
  have hscaled : (principalCoefficient g x).toQuadraticForm' (‖ξ‖⁻¹ • ξ) =
      ‖ξ‖⁻¹ ^ 2 * (principalCoefficient g x).toQuadraticForm' ξ := by
    simpa [pow_two, smul_eq_mul] using
      (principalCoefficient g x).toQuadraticForm'.map_smul ‖ξ‖⁻¹ (ξ : Fin 3 → ℝ)
  have hb' : lam ≤ ‖ξ‖⁻¹ ^ 2 * (principalCoefficient g x).toQuadraticForm' ξ := by
    rw [← hscaled]
    simpa only [Q, Matrix.toQuadraticForm'_apply, WithLp.ofLp_smul] using hb
  have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖ξ‖)
  have he : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ ^ 2 * (principalCoefficient g x).toQuadraticForm' ξ) =
      (principalCoefficient g x).toQuadraticForm' ξ := by
    field_simp [hn]
  rw [he] at hm
  simpa only [mul_comm] using hm

/-- The exact Tau uniform ellipticity interface on the closed unit ball, from frozen admissibility. -/
theorem exists_uniformlyEllipticOn_principalCoefficient (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    ∃ lam Λ : ℝ, TauCeti.PDE.UniformlyEllipticOn (Metric.closedBall (0 : R3) 1)
      (principalCoefficient g) lam Λ := by
  obtain ⟨lam, hlam, hlower⟩ := exists_principalCoefficient_lower_bound g hg
  obtain ⟨M, hM, hupper⟩ := exists_principalCoefficient_upper_bound g hg
  refine ⟨lam, max M lam, hlam, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨hlower x hx, ?_⟩
  intro η ξ
  exact (hupper x hx η ξ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left M lam) (norm_nonneg η)) (norm_nonneg ξ))

/-- The same constants restrict to the exact frozen open ball. -/
theorem exists_uniformlyEllipticOn_principalCoefficient_ball (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    ∃ lam Λ : ℝ, TauCeti.PDE.UniformlyEllipticOn B (principalCoefficient g) lam Λ := by
  obtain ⟨lam, Λ, h⟩ := exists_uniformlyEllipticOn_principalCoefficient g hg
  exact ⟨lam, Λ, h.mono_set Metric.ball_subset_closedBall⟩

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.exists_principalCoefficient_lower_bound
#print axioms OAI.AnisotropicCalderon.EnergyBridge.exists_uniformlyEllipticOn_principalCoefficient

#print axioms OAI.AnisotropicCalderon.EnergyBridge.exists_uniformlyEllipticOn_principalCoefficient_ball
