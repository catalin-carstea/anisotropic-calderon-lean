import Calderon.DilatedDepthUniform

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

lemma inverseMetricOperator_dilatedReference (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam L : ℝ) (x : R3) :
    inverseMetricOperator (referenceMetric (dilatedMetric g lam) L) x =
      Real.exp (2 * L * referenceCoordinateDepth x) • inverseMetricOperator g (lam • x) := by
  rw [referenceMetric, inverseMetricOperator_conformalMatrix _ _ (dilatedMetric_posDef g hg lam),
    dilatedMetric_inverse_eq]
  congr 1
  congr 1
  ring

lemma continuous_dilatedReferenceDepth_metricNorm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : Continuous (fun z : ℝ × R3 =>
      metricDifferentialNorm (referenceMetric (dilatedMetric g z.1) L) (referenceDepth L) z.2) := by
  have hQ : Continuous (fun z : ℝ × R3 => inverseMetricOperator g (z.1 • z.2)) :=
    (contDiff_inverseMetricOperator g hg).continuous.comp (continuous_fst.smul continuous_snd)
  have ha : Continuous (fun z : ℝ × R3 => Real.exp (2 * L * referenceCoordinateDepth z.2)) :=
    Real.continuous_exp.comp
      (continuous_const.mul (contDiff_referenceCoordinateDepth.continuous.comp continuous_snd))
  have hI : Continuous (fun z : ℝ × R3 =>
      inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) := by
    have he : (fun z : ℝ × R3 => inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) =
        fun z => Real.exp (2 * L * referenceCoordinateDepth z.2) • inverseMetricOperator g (z.1 • z.2) :=
      funext (fun z => inverseMetricOperator_dilatedReference g hg z.1 L z.2)
    rw [he]
    exact ha.smul hQ
  have hG : Continuous (fun z : ℝ × R3 => gradient (referenceDepth L) z.2) :=
    ((contDiff_referenceDepth L).gradient_right (m := 0) (by simp)).continuous.comp continuous_snd
  exact Real.continuous_sqrt.comp ((hI.clm_apply hG).inner hG)

lemma exists_dilatedReferenceDepth_uniform_metricNorm_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ m C T : ℝ, 0 < m ∧ 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      m ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x ∧
      metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L) (referenceDepth L) x ≤ C ∧
      referenceDepth L x ≤ T := by
  have hb := continuous_dilatedReferenceDepth_metricNorm g hg L
  have hp : ∀ z : ℝ × R3, (referenceMetric (dilatedMetric g z.1) L z.2).PosDef :=
    fun z => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg z.1) z.2
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc.prod hK).exists_forall_le' hb.continuousOn (a := (0 : ℝ))
    (fun z _ => metricDifferentialNorm_pos _
      (fun y => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg z.1) y)
      _ z.2 (fderiv_referenceDepth_ne_zero L (ne_of_gt hL) z.2))
  obtain ⟨A, hmax⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨T, ht⟩ := hK.exists_bound_of_continuousOn (contDiff_referenceDepth L).continuous.continuousOn
  refine ⟨m, max A 0 + 1, T, hm, by positivity, ?_⟩
  intro lam hlam x hx
  refine ⟨hmin (lam, x) ⟨hlam, hx⟩, ?_, (le_abs_self _).trans (ht x hx)⟩
  have h := (le_abs_self _).trans (hmax (lam, x) ⟨hlam, hx⟩)
  exact h.trans (by linarith [le_max_left A 0])

theorem exists_dilated_referenceRadius_uniform_metric_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c0 c1 C T : ℝ, 0 < L ∧ 0 < c0 ∧ 0 < c1 ∧ 0 < C ∧
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
  obtain ⟨L, hL, hdepth⟩ := exists_dilated_referenceDepth_uniform_strict_hessian_bound g hg K hK
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha : 0 < a := by
    dsimp [a]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  refine ⟨L, a * m, 1 / C, C, T, hL, mul_pos ha hm, one_div_pos.mpr hC, hC, ?_⟩
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

end OAI.AnisotropicCalderon.ConformalDepth
