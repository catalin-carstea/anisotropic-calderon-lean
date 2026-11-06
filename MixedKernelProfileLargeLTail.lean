import TaskInterface
import Calderon.DilatedProfileUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open AngularPolynomial ConformalDepth RadiusProfile MetricOperator ConnectionError
open scoped ContDiff InnerProductSpace Topology

/-- The SAME native conformal depth is strictly concave for EVERY sufficiently large L. -/
theorem exists_dilated_referenceDepth_uniform_strict_hessian_tail
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
        -⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ := by
  obtain ⟨m, hm, hq⟩ := exists_dilatedCoordinateDepth_uniform_metricSquare_lower_bound g hg K hK
  obtain ⟨C, hC, hess⟩ := exists_dilatedCoordinateDepth_uniform_hessian_upper_bound g hg K hK
  obtain ⟨L0, hL0, hchoice⟩ := exists_conformal_depth_parameter C 1 m hC (by norm_num) hm
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨L0, hL0, ?_⟩
  intro L hLL
  have hL : 0 < L := hL0.trans_le hLL
  have hchoiceTail : C-L*m ≤ -(1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hLL hm.le
    linarith [hchoice]
  intro lam hlam x hx X
  rw [referenceDepth_coordinateHessian_of_smooth_posDef _ (dilatedMetric_smooth_entries g hg lam)
    (dilatedMetric_posDef g hg lam) L (ne_of_gt hL), referenceMetric_operator_eq]
  simp only [smul_apply, real_inner_smul_left]
  have hdiag : 0 ≤ ⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ :=
    (mul_nonneg hd.le (sq_nonneg ‖X‖)).trans (hmetric (lam • x) X)
  have h := conformal_depth_hessian_le (Real.exp (-2 * L * referenceCoordinateDepth x))
    L C 1 m
    (coordinateHessian referenceCoordinateDepth
      (fun V W => coordinateConnectionField (inverseMetricOperator (dilatedMetric g lam))
        (metricOperatorField (dilatedMetric g lam)) x V W) x X X)
    ⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ
    (fderiv ℝ referenceCoordinateDepth x
      (metricGradient (inverseMetricOperator (dilatedMetric g lam) x) (fderiv ℝ referenceCoordinateDepth x)))
    (Real.exp_pos _).le hL.le hdiag (hess lam hlam x hx X) (hq lam hlam x hx) hchoiceTail
  simpa only [neg_one_mul] using h


/-- All native profile constants now respect the ORIGINAL universal large-L quantifier. -/
theorem exists_dilated_referenceRadius_uniform_metric_tail
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ c0 c1 C T : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p j : ℕ, j ≤ p → ∀ x ∈ K,
        c0 * (p : ℝ) ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y)) x ∧
        (∀ X : R3, coordinateHessian (fun y => Real.log (referenceRadius δ R p L y))
          (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
            (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
          -c1 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x *
              ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ j ≤
          R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  obtain ⟨L0,hL0,Htail⟩ := exists_dilated_referenceDepth_uniform_strict_hessian_tail g hg K hK
  refine ⟨L0,hL0,?_⟩
  intro L hLL
  have hL : 0 < L := hL0.trans_le hLL
  have hdepth := Htail L hLL
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha : 0 < a := by
    dsimp [a]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  refine ⟨a * m, 1 / C, C, T, mul_pos ha hm, one_div_pos.mpr hC, hC, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p j hj x hx
  rw [log_referenceRadius δ R p L hδ hR]
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have hb : 0 ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x := Real.sqrt_nonneg _
  have hbound : metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x ≤
      (p : ℝ) * C * logSlope δ (referenceDepth L x) := by
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have h := mul_le_mul_of_nonneg_left hmax
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (referenceDepth L x) hδ).le)
    convert h using 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have hs : a ≤ logSlope δ (referenceDepth L x) := logSlope_uniform_lower_bound δ _ T hδ hδ1 ht
    have h1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg p)
    have h2 := mul_le_mul h1 hmin hm.le
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ _ hδ).le)
    convert h2 using 1 <;> ring
  · intro X
    exact coordinateHessian_logProfile_metric_le _
      (fun y => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg lam) y)
      δ (Real.log R) C p _ (contDiff_referenceDepth L) x X hδ hC hmax (hdepth lam hlam x hx X)
  · exact radius_gradient_power_uniform_scale_bound δ _ T R C _ p j hδ hδ1 ht hR.le hC.le hb hj hbound


end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
