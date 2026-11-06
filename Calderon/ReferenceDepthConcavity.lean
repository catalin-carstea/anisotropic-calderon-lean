import Calderon.ReferenceConformalDepth
import Calderon.MetricGeodesicEnergy

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

lemma referenceCoordinateDepth_metricSquare_pos (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x : R3) : 0 < fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x)) := by
  have hn : gradient referenceCoordinateDepth x ≠ 0 := by
    intro h
    have he := fderiv_referenceCoordinateDepth_normal x
    rw [← inner_gradient_left, h, inner_zero_left] at he
    norm_num at he
  have he : fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x)) =
      coefficientQuadratic (inverseMetricOperator g) x (gradient referenceCoordinateDepth x) := by
    rw [← inner_gradient_left, real_inner_comm]
    rfl
  rw [he, coefficientQuadratic_inverseMetricOperator g hg, TauCeti.PDE.matrixBilinearForm_apply]
  apply (hg.posDef x).inv.dotProduct_mulVec_pos
  intro h
  apply hn
  ext i
  exact congrFun h i

lemma referenceCoordinateDepth_metricSquare_continuous (g : MatrixField)
    (hg : IsAdmissibleMetric g) :
    Continuous (fun x => fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x))) := by
  have he : (fun x => fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x))) =
      fun x => coefficientQuadratic (inverseMetricOperator g) x
        (gradient referenceCoordinateDepth x) := by
    funext x
    rw [← inner_gradient_left, real_inner_comm]
    rfl
  rw [he]
  have hG := (contDiff_referenceCoordinateDepth.gradient_right (m := 0) (by simp)).continuous
  exact ((contDiff_inverseMetricOperator g hg).continuous.clm_apply hG).inner hG

lemma exists_referenceCoordinateDepth_metricSquare_lower_bound_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x)) :=
  hK.exists_forall_le' (referenceCoordinateDepth_metricSquare_continuous g hg).continuousOn
    (a := (0 : ℝ)) (fun x _ => referenceCoordinateDepth_metricSquare_pos g hg x)

lemma exists_referenceCoordinateDepth_hessian_upper_bound_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ X : R3,
      coordinateHessian referenceCoordinateDepth
        (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
          x V W) x X X ≤ C * ⟪metricOperatorField g x X, X⟫_ℝ := by
  let F : R3 × R3 → ℝ := fun z => coordinateHessian referenceCoordinateDepth
    (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
      z.1 V W) z.1 z.2 z.2
  have hD := (contDiff_infty_iff_fderiv.mp contDiff_referenceCoordinateDepth).2
  have hDD := (contDiff_infty_iff_fderiv.mp hD).2
  have hConn : Continuous (coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)) :=
    (contDiff_coordinateConnectionField_infty _ _ (contDiff_inverseMetricOperator g hg)
      (contDiff_metricOperatorField g hg)).continuous
  have hF : Continuous F :=
    (((hDD.continuous.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd).sub
      ((hD.continuous.comp continuous_fst).clm_apply
        (((hConn.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd))
  obtain ⟨A, hA⟩ := (hK.prod (isCompact_sphere (0 : R3) 1)).exists_bound_of_continuousOn hF.continuousOn
  let N : ℝ := max A 0
  have hN : 0 ≤ N := le_max_right _ _
  have hnorm : ∀ x ∈ K, ∀ X : R3, F (x, X) ≤ N * ‖X‖ ^ 2 := by
    intro x hx X
    by_cases hX : X = 0
    · simp [F, coordinateHessian, hX]
    have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
    have hunit : (‖X‖⁻¹ • X : R3) ∈ Metric.sphere 0 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hb : F (x, ‖X‖⁻¹ • X) ≤ N :=
      (le_abs_self _).trans ((hA (x, ‖X‖⁻¹ • X) ⟨hx, hunit⟩).trans (le_max_left A 0))
    have hscale : F (x, ‖X‖⁻¹ • X) = ‖X‖⁻¹ ^ 2 * F (x, X) := by
      simp only [F, coordinateHessian, map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hscale] at hb
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖X‖)
    have he : ‖X‖ ^ 2 * (‖X‖⁻¹ ^ 2 * F (x, X)) = F (x, X) := by field_simp [hn]
    rw [he] at hm
    simpa only [mul_comm] using hm
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨N / d, div_nonneg hN hd.le, ?_⟩
  intro x hx X
  have hm := mul_le_mul_of_nonneg_left (hmetric x X) (div_nonneg hN hd.le)
  have he : (N / d) * (d * ‖X‖ ^ 2) = N * ‖X‖ ^ 2 := by field_simp
  rw [he] at hm
  exact (hnorm x hx X).trans hm

theorem exists_referenceDepth_strict_hessian_bound_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ X : R3,
      coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric g L))
          (metricOperatorField (referenceMetric g L)) x V W) x X X ≤
        -⟪metricOperatorField (referenceMetric g L) x X, X⟫_ℝ := by
  obtain ⟨m, hm, hq⟩ := exists_referenceCoordinateDepth_metricSquare_lower_bound_on_compact g hg K hK
  obtain ⟨C, hC, hess⟩ := exists_referenceCoordinateDepth_hessian_upper_bound_on_compact g hg K hK
  obtain ⟨L, hL, hchoice⟩ := exists_conformal_depth_parameter C 1 m hC (by norm_num) hm
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨L, hL, ?_⟩
  intro x hx X
  rw [referenceDepth_coordinateHessian g hg L (ne_of_gt hL), referenceMetric_operator_eq]
  simp only [smul_apply, real_inner_smul_left]
  have hdiag : 0 ≤ ⟪metricOperatorField g x X, X⟫_ℝ :=
    (mul_nonneg hd.le (sq_nonneg ‖X‖)).trans (hmetric x X)
  have h := conformal_depth_hessian_le (Real.exp (-2 * L * referenceCoordinateDepth x))
    L C 1 m
    (coordinateHessian referenceCoordinateDepth
      (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
        x V W) x X X)
    ⟪metricOperatorField g x X, X⟫_ℝ
    (fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x)))
    (Real.exp_pos _).le hL.le hdiag (hess x hx X) (hq x hx) (by rw [hchoice])
  simpa only [neg_one_mul] using h

end OAI.AnisotropicCalderon.ConformalDepth
