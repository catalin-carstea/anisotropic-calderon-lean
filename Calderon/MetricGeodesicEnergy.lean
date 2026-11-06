import Calderon.MetricOperator
import Mathlib.Analysis.Calculus.MeanValue
import Calderon.MetricUniform
import Mathlib.Tactic

open scoped ContDiff
open Matrix
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError

theorem metricOperatorField_inner_eq_quadratic (g : MatrixField) (x X : R3) :
    inner ℝ (metricOperatorField g x X) X = (g x).toQuadraticForm' (X : Fin 3 → ℝ) := by
  rw [metricOperatorField_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, Matrix.toQuadraticForm'_apply]
  congr 1

theorem metric_geodesic_energy_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (q v : ℝ → R3) (a b s t : ℝ)
    (hq : ∀ z ∈ Set.Ioo a b, HasDerivAt q (v z) z)
    (hv : ∀ z ∈ Set.Ioo a b, HasDerivAt v (-coordinateConnectionField
      (inverseMetricField (metricOperatorField g)) (metricOperatorField g)
      (q z) (v z) (v z)) z)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    inner ℝ (metricOperatorField g (q s) (v s)) (v s) =
      inner ℝ (metricOperatorField g (q t) (v t)) (v t) := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun z =>
    inner ℝ (metricOperatorField g (q z) (v z)) (v z))
    (convex_Ioo a b).isPreconnected
  · intro z hz
    exact (hasDerivAt_metric_geodesic_energy_zero g hg q v z
      (hq z hz) (hv z hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_metric_geodesic_energy_zero g hg q v z
      (hq z hz) (hv z hz)).deriv
  · exact hs
  · exact ht

theorem exists_metricOperatorField_global_lower_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    ∃ c : ℝ, 0 < c ∧ ∀ x X : R3,
      c * ‖X‖^2 ≤ inner ℝ (metricOperatorField g x X) X := by
  let F : R3 × R3 → ℝ := fun z => inner ℝ (metricOperatorField g z.1 z.2) z.2
  have hF : Continuous F :=
    (((contDiff_metricOperatorField g hg).continuous.comp continuous_fst).clm_apply
      continuous_snd).inner continuous_snd
  have hK := (isCompact_closedBall (0 : R3) 1).prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨c, hc, hbound⟩ := hK.exists_forall_le' hF.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hn : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hne : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro h
      have he : z.2 = 0 := by ext i; exact congrFun h i
      simp [he] at hn
    change 0 < inner ℝ (metricOperatorField g z.1 z.2) z.2
    rw [metricOperatorField_inner_eq_quadratic, Matrix.toQuadraticForm'_apply]
    exact (hg.posDef z.1).dotProduct_mulVec_pos hne)
  have hinside : ∀ x ∈ Metric.closedBall (0 : R3) 1, ∀ X : R3,
      c * ‖X‖^2 ≤ inner ℝ (metricOperatorField g x X) X := by
    intro x hx X
    by_cases hX : X = 0
    · simp [hX]
    have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
    have hsphere : (‖X‖⁻¹ • X : R3) ∈ Metric.sphere 0 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hh := hbound (x, ‖X‖⁻¹ • X) ⟨hx, hsphere⟩
    have hscale : F (x, ‖X‖⁻¹ • X) = ‖X‖⁻¹^2 * F (x,X) := by
      simp only [F, map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hscale] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖X‖)
    have he : ‖X‖^2 * (‖X‖⁻¹^2 * F (x,X)) = F (x,X) := by field_simp [hn]
    rw [he] at hm
    simpa only [F, mul_comm] using hm
  refine ⟨min c 1, lt_min hc (by norm_num), ?_⟩
  intro x X
  by_cases hx : ‖x‖ ≤ 1
  · exact (mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg ‖X‖)).trans
      (hinside x (mem_closedBall_zero_iff.mpr hx) X)
  · have hge : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    rw [metricOperatorField_inner_eq_quadratic, hg.euclidean_exterior x hge]
    have hid : (1 : Matrix (Fin 3) (Fin 3) ℝ).toQuadraticForm' (X : Fin 3 → ℝ) = ‖X‖^2 := by
      rw [← metricOperatorField_inner_eq_quadratic (fun _ => 1) x X]
      change inner ℝ (matrixOperatorAlgEquiv (1 : Matrix (Fin 3) (Fin 3) ℝ) X) X = _
      rw [map_one, one_apply_eq_self]
      exact real_inner_self_eq_norm_sq X
    rw [hid]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_right c 1) (sq_nonneg ‖X‖)

theorem exists_metric_geodesic_velocity_bound (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q v : ℝ → R3) (a b s : ℝ),
      (∀ z ∈ Set.Ioo a b, HasDerivAt q (v z) z) →
      (∀ z ∈ Set.Ioo a b, HasDerivAt v (-coordinateConnectionField
        (inverseMetricField (metricOperatorField g)) (metricOperatorField g)
        (q z) (v z) (v z)) z) → s ∈ Set.Ioo a b →
      ∀ t ∈ Set.Ioo a b, ‖v t‖^2 ≤
        inner ℝ (metricOperatorField g (q s) (v s)) (v s) / c := by
  obtain ⟨c,hc,hbound⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨c,hc,?_⟩
  intro q v a b s hq hv hs t ht
  apply (le_div_iff₀ hc).mpr
  have h := hbound (q t) (v t)
  rw [← metric_geodesic_energy_eq g hg q v a b s t hq hv hs ht] at h
  simpa only [mul_comm] using h

#print axioms metricOperatorField_inner_eq_quadratic
#print axioms metric_geodesic_energy_eq
#print axioms exists_metricOperatorField_global_lower_bound
#print axioms exists_metric_geodesic_velocity_bound
end OAI.AnisotropicCalderon.MetricOperator
