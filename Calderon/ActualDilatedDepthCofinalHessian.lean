import Calderon.DilatedDepthUniform

/-! Cofinal strict concavity for the actual conformal depth. No coercivity claim. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

/-- The same actual depth is strictly concave for every sufficiently large conformal
parameter, uniformly over the original compact base set and coefficient dilations. -/
theorem exists_dilated_referenceDepth_strict_hessian_bound_forall_ge
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
        coordinateHessian (referenceDepth L)
          (fun V W => coordinateConnectionField
            (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
            (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
          -⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ := by
  obtain ⟨m, hm, hq⟩ := exists_dilatedCoordinateDepth_uniform_metricSquare_lower_bound g hg K hK
  obtain ⟨C, hC, hess⟩ := exists_dilatedCoordinateDepth_uniform_hessian_upper_bound g hg K hK
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  let L0 : ℝ := (C + 1) / m
  have hL0 : 0 < L0 := div_pos (by positivity) hm
  refine ⟨L0, hL0, ?_⟩
  intro L hLge lam hlam x hx X
  have hL : 0 < L := hL0.trans_le hLge
  have hLm : C + 1 ≤ L * m := (div_le_iff₀ hm).mp hLge
  have hdiag : 0 ≤ ⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ :=
    (mul_nonneg hd.le (sq_nonneg ‖X‖)).trans (hmetric (lam • x) X)
  have hLq := mul_le_mul_of_nonneg_left (hq lam hlam x hx) hL.le
  have hLqdiag := mul_le_mul_of_nonneg_right hLq hdiag
  have hLmdiag := mul_le_mul_of_nonneg_right hLm hdiag
  have hbase := hess lam hlam x hx X
  have hinner :
      coordinateHessian referenceCoordinateDepth
        (fun V W => coordinateConnectionField (inverseMetricOperator (dilatedMetric g lam))
          (metricOperatorField (dilatedMetric g lam)) x V W) x X X -
        L * (fderiv ℝ referenceCoordinateDepth x
          (metricGradient (inverseMetricOperator (dilatedMetric g lam) x)
            (fderiv ℝ referenceCoordinateDepth x))) *
          ⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ ≤
        -⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ := by
    nlinarith
  rw [referenceDepth_coordinateHessian_of_smooth_posDef _ (dilatedMetric_smooth_entries g hg lam)
    (dilatedMetric_posDef g hg lam) L (ne_of_gt hL), referenceMetric_operator_eq]
  simp only [smul_apply, real_inner_smul_left]
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left hinner
    (Real.exp_pos (-2 * L * referenceCoordinateDepth x)).le

end OAI.AnisotropicCalderon.ConformalDepth
#print axioms OAI.AnisotropicCalderon.ConformalDepth.exists_dilated_referenceDepth_strict_hessian_bound_forall_ge
