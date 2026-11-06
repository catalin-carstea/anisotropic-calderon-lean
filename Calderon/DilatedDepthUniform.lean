import Calderon.ReferenceRadiusScaling

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

/-- The normalized coefficient dilation used by the manuscript. -/
def dilatedMetric (g : MatrixField) (lam : ℝ) : MatrixField := fun x => g (lam • x)

lemma dilatedMetric_smooth_entries (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (i j : Fin 3) : ContDiff ℝ ∞ (fun x => dilatedMetric g lam x i j) :=
  (hg.smooth i j).comp (contDiff_id.const_smul lam)

lemma dilatedMetric_posDef (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (x : R3) : (dilatedMetric g lam x).PosDef := hg.posDef (lam • x)

lemma dilatedMetric_operator_eq (g : MatrixField) (lam : ℝ) (x : R3) :
    metricOperatorField (dilatedMetric g lam) x = metricOperatorField g (lam • x) := rfl

lemma dilatedMetric_inverse_eq (g : MatrixField) (lam : ℝ) (x : R3) :
    inverseMetricOperator (dilatedMetric g lam) x = inverseMetricOperator g (lam • x) := rfl

lemma fderiv_dilatedMetricOperator (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (x : R3) :
    fderiv ℝ (metricOperatorField (dilatedMetric g lam)) x =
      lam • fderiv ℝ (metricOperatorField g) (lam • x) := by
  have h := (((contDiff_metricOperatorField g hg).differentiable (by simp) (lam • x)).hasFDerivAt).comp x
    ((lam • ContinuousLinearMap.id ℝ R3).hasFDerivAt (x := x))
  change HasFDerivAt (metricOperatorField (dilatedMetric g lam)) _ x at h
  rw [h.fderiv]
  ext V
  simp

lemma dilatedMetric_connection_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (x X Y : R3) :
    coordinateConnectionField (inverseMetricOperator (dilatedMetric g lam))
        (metricOperatorField (dilatedMetric g lam)) x X Y =
      lam • coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g) (lam • x) X Y := by
  simp only [coordinateConnectionField_apply, dilatedMetric_inverse_eq,
    fderiv_dilatedMetricOperator g hg]
  have hk : koszulFunctional (lam • fderiv ℝ (metricOperatorField g) (lam • x)) X Y =
      lam • koszulFunctional (fderiv ℝ (metricOperatorField g) (lam • x)) X Y := by
    ext Z
    simp only [koszulFunctional_apply, smul_apply, real_inner_smul_left, smul_eq_mul]
    ring
  simp only [coordinateConnection, hk, map_smul, smul_smul]
  congr 1
  ring

lemma referenceDepth_coordinateHessian_of_smooth_posDef (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (L : ℝ) (hL : L ≠ 0) (x X Y : R3) :
    coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric g L))
          (metricOperatorField (referenceMetric g L)) x V W) x X Y =
      Real.exp (-2 * L * referenceCoordinateDepth x) *
        (coordinateHessian referenceCoordinateDepth
          (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
            x V W) x X Y -
            L * (fderiv ℝ referenceCoordinateDepth x
              (metricGradient (inverseMetricOperator g x) (fderiv ℝ referenceCoordinateDepth x))) *
                ⟪metricOperatorField g x X, Y⟫_ℝ) := by
  have hfield : ContDiff ℝ ∞ g :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => hs i j))
  have hM : ContDiff ℝ ∞ (metricOperatorField g) := matrixOperatorMap.contDiff.comp hfield
  have hunit : ∀ y, IsUnit (metricOperatorField g y) :=
    fun y => (hp y).isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  have hsym : ∀ V W, ⟪metricOperatorField g x V, W⟫_ℝ = ⟪metricOperatorField g x W, V⟫_ℝ := by
    intro V W
    have h := Matrix.isSymmetric_toEuclideanLin_iff.mpr (hp x).isHermitian
    exact (h V W).trans (real_inner_comm _ _)
  have hi : inverseMetricOperator (referenceMetric g L) x =
      (Real.exp (-2 * L * referenceCoordinateDepth x))⁻¹ • inverseMetricOperator g x := by
    rw [referenceMetric, inverseMetricOperator_conformalMatrix g _ hp]
    congr 1
    rw [← Real.exp_neg]
    congr 1
    ring
  have hDgamma : fderiv ℝ (metricOperatorField (referenceMetric g L)) x =
      conformalMetricDerivative (Real.exp (-2 * L * referenceCoordinateDepth x)) L
        (metricOperatorField g x) (fderiv ℝ (metricOperatorField g) x)
        (fderiv ℝ referenceCoordinateDepth x) := by
    have he : metricOperatorField (referenceMetric g L) =
        fun y => Real.exp (-2 * L * referenceCoordinateDepth y) • metricOperatorField g y :=
      funext (referenceMetric_operator_eq g L)
    rw [he]
    exact (hasFDerivAt_conformalMetric L referenceCoordinateDepth (metricOperatorField g) x _ _
      (contDiff_referenceCoordinateDepth.differentiable (by simp) x).hasFDerivAt
      (hM.differentiable (by simp) x).hasFDerivAt).fderiv
  have hsecond := (contDiff_infty_iff_fderiv.mp contDiff_referenceCoordinateDepth).2
  have ht := (contDiff_referenceCoordinateDepth.differentiable (by simp) x).hasFDerivAt
  have hH := (hsecond.differentiable (by simp) x).hasFDerivAt
  have hn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ referenceCoordinateDepth y :=
    Filter.Eventually.of_forall (contDiff_referenceCoordinateDepth.differentiable (by simp))
  simp only [coordinateConnectionField_apply]
  change coordinateHessian (depthFunction L (1 / 8) referenceCoordinateDepth)
    (coordinateConnection (inverseMetricOperator (referenceMetric g L) x)
      (fderiv ℝ (metricOperatorField (referenceMetric g L)) x)) x X Y = _
  rw [hi, hDgamma]
  exact coordinateHessian_depthFunction L (1 / 8) referenceCoordinateDepth x _ _ _ _ _ hL ht hH hn
    (fun V => inverseMetricField_apply_metric _ hunit x V)
    (fun V => metric_apply_inverseMetricField _ hunit x V) hsym X Y

lemma continuous_dilatedCoordinateDepth_metricSquare (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (fun z : ℝ × R3 => fderiv ℝ referenceCoordinateDepth z.2
      (metricGradient (inverseMetricOperator (dilatedMetric g z.1) z.2)
        (fderiv ℝ referenceCoordinateDepth z.2))) := by
  have he : (fun z : ℝ × R3 => fderiv ℝ referenceCoordinateDepth z.2
      (metricGradient (inverseMetricOperator (dilatedMetric g z.1) z.2)
        (fderiv ℝ referenceCoordinateDepth z.2))) =
      fun z => coefficientQuadratic (inverseMetricOperator g) (z.1 • z.2)
        (gradient referenceCoordinateDepth z.2) := by
    funext z
    rw [← inner_gradient_left, real_inner_comm]
    rfl
  rw [he]
  have hG : Continuous (fun z : ℝ × R3 => gradient referenceCoordinateDepth z.2) :=
    (contDiff_referenceCoordinateDepth.gradient_right (m := 0) (by simp)).continuous.comp continuous_snd
  have hQ : Continuous (fun z : ℝ × R3 => inverseMetricOperator g (z.1 • z.2)) :=
    (contDiff_inverseMetricOperator g hg).continuous.comp (continuous_fst.smul continuous_snd)
  exact (hQ.clm_apply hG).inner hG

lemma exists_dilatedCoordinateDepth_uniform_metricSquare_lower_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      m ≤ fderiv ℝ referenceCoordinateDepth x
        (metricGradient (inverseMetricOperator (dilatedMetric g lam) x)
          (fderiv ℝ referenceCoordinateDepth x)) := by
  have hpos : ∀ z : ℝ × R3, 0 < fderiv ℝ referenceCoordinateDepth z.2
      (metricGradient (inverseMetricOperator (dilatedMetric g z.1) z.2)
        (fderiv ℝ referenceCoordinateDepth z.2)) := by
    intro z
    have h := metricDifferentialNorm_pos (dilatedMetric g z.1) (dilatedMetric_posDef g hg z.1)
      referenceCoordinateDepth z.2 (fderiv_referenceCoordinateDepth_ne_zero z.2)
    have hq := Real.sqrt_pos.mp h
    rw [← inner_gradient_left, real_inner_comm]
    exact hq
  obtain ⟨m, hm, hbound⟩ := (isCompact_Icc.prod hK).exists_forall_le'
    (continuous_dilatedCoordinateDepth_metricSquare g hg).continuousOn (a := (0 : ℝ)) (fun z _ => hpos z)
  exact ⟨m, hm, fun lam hlam x hx => hbound (lam, x) ⟨hlam, hx⟩⟩

lemma exists_dilatedCoordinateDepth_uniform_hessian_upper_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      coordinateHessian referenceCoordinateDepth
        (fun V W => coordinateConnectionField (inverseMetricOperator (dilatedMetric g lam))
          (metricOperatorField (dilatedMetric g lam)) x V W) x X X ≤
        C * ⟪metricOperatorField (dilatedMetric g lam) x X, X⟫_ℝ := by
  let F : (ℝ × R3) × R3 → ℝ := fun z => coordinateHessian referenceCoordinateDepth
    (fun V W => coordinateConnectionField (inverseMetricOperator (dilatedMetric g z.1.1))
      (metricOperatorField (dilatedMetric g z.1.1)) z.1.2 V W) z.1.2 z.2 z.2
  have hD := (contDiff_infty_iff_fderiv.mp contDiff_referenceCoordinateDepth).2
  have hDD := (contDiff_infty_iff_fderiv.mp hD).2
  have hConn : Continuous (coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)) :=
    (contDiff_coordinateConnectionField_infty _ _ (contDiff_inverseMetricOperator g hg)
      (contDiff_metricOperatorField g hg)).continuous
  have hlam : Continuous (fun z : (ℝ × R3) × R3 => z.1.1) := continuous_fst.comp continuous_fst
  have hx : Continuous (fun z : (ℝ × R3) × R3 => z.1.2) := continuous_snd.comp continuous_fst
  have hF : Continuous F := by
    have he : F = fun z => fderiv ℝ (fderiv ℝ referenceCoordinateDepth) z.1.2 z.2 z.2 -
        fderiv ℝ referenceCoordinateDepth z.1.2
          (z.1.1 • coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
            (z.1.1 • z.1.2) z.2 z.2) := by
      funext z
      unfold F coordinateHessian
      dsimp only
      rw [dilatedMetric_connection_eq g hg]
    rw [he]
    exact (((hDD.continuous.comp hx).clm_apply continuous_snd).clm_apply continuous_snd).sub
      ((hD.continuous.comp hx).clm_apply
        (hlam.smul (((hConn.comp (hlam.smul hx)).clm_apply continuous_snd).clm_apply continuous_snd)))
  obtain ⟨A, hA⟩ := ((isCompact_Icc.prod hK).prod (isCompact_sphere (0 : R3) 1)).exists_bound_of_continuousOn hF.continuousOn
  let N : ℝ := max A 0
  have hN : 0 ≤ N := le_max_right _ _
  have hnorm : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      F ((lam, x), X) ≤ N * ‖X‖ ^ 2 := by
    intro lam hlam x hx X
    by_cases hX : X = 0
    · simp [F, coordinateHessian, hX]
    have hn : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
    have hunit : (‖X‖⁻¹ • X : R3) ∈ Metric.sphere 0 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hb : F ((lam, x), ‖X‖⁻¹ • X) ≤ N :=
      (le_abs_self _).trans ((hA ((lam, x), ‖X‖⁻¹ • X) ⟨⟨hlam, hx⟩, hunit⟩).trans (le_max_left A 0))
    have hscale : F ((lam, x), ‖X‖⁻¹ • X) = ‖X‖⁻¹ ^ 2 * F ((lam, x), X) := by
      simp only [F, coordinateHessian, map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hscale] at hb
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖X‖)
    have he : ‖X‖ ^ 2 * (‖X‖⁻¹ ^ 2 * F ((lam, x), X)) = F ((lam, x), X) := by field_simp [hn]
    rw [he] at hm
    simpa only [mul_comm] using hm
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨N / d, div_nonneg hN hd.le, ?_⟩
  intro lam hlam x hx X
  rw [dilatedMetric_operator_eq]
  have hm := mul_le_mul_of_nonneg_left (hmetric (lam • x) X) (div_nonneg hN hd.le)
  have he : (N / d) * (d * ‖X‖ ^ 2) = N * ‖X‖ ^ 2 := by field_simp
  rw [he] at hm
  exact (hnorm lam hlam x hx X).trans hm

theorem exists_dilated_referenceDepth_uniform_strict_hessian_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
        -⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ := by
  obtain ⟨m, hm, hq⟩ := exists_dilatedCoordinateDepth_uniform_metricSquare_lower_bound g hg K hK
  obtain ⟨C, hC, hess⟩ := exists_dilatedCoordinateDepth_uniform_hessian_upper_bound g hg K hK
  obtain ⟨L, hL, hchoice⟩ := exists_conformal_depth_parameter C 1 m hC (by norm_num) hm
  obtain ⟨d, hd, hmetric⟩ := exists_metricOperatorField_global_lower_bound g hg
  refine ⟨L, hL, ?_⟩
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
    (Real.exp_pos _).le hL.le hdiag (hess lam hlam x hx X) (hq lam hlam x hx) (by rw [hchoice])
  simpa only [neg_one_mul] using h

end OAI.AnisotropicCalderon.ConformalDepth
