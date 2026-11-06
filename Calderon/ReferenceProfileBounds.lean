import Calderon.ReferenceDepthConcavity
import Calderon.ProfileUniform

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

/-- The true covector norm, using the actual inverse metric and Riesz gradient. -/
def metricDifferentialNorm (g : MatrixField) (u : R3 → ℝ) (x : R3) : ℝ :=
  Real.sqrt (coefficientQuadratic (inverseMetricOperator g) x (gradient u x))

lemma continuous_metricDifferentialNorm (g : MatrixField)
    (hs : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hp : ∀ x, (g x).PosDef)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) : Continuous (metricDifferentialNorm g u) := by
  have hG := (hu.gradient_right (m := 0) (by simp)).continuous
  exact Real.continuous_sqrt.comp
    (((contDiff_inverseMetricOperator_of_smooth_posDef g hs hp).continuous.clm_apply hG).inner hG)

lemma metricDifferentialNorm_pos (g : MatrixField) (hp : ∀ x, (g x).PosDef)
    (u : R3 → ℝ) (x : R3) (hdu : fderiv ℝ u x ≠ 0) :
    0 < metricDifferentialNorm g u x := by
  have hn : gradient u x ≠ 0 := by
    intro h
    apply hdu
    rw [← toDual_gradient, h, map_zero]
  unfold metricDifferentialNorm
  apply Real.sqrt_pos.mpr
  rw [coefficientQuadratic_inverseMetricOperator_of_posDef g hp,
    TauCeti.PDE.matrixBilinearForm_apply]
  apply (hp x).inv.dotProduct_mulVec_pos
  intro h
  apply hn
  ext i
  exact congrFun h i

lemma metricDifferentialNorm_logProfile (g : MatrixField) (δ c : ℝ) (p : ℕ)
    (u : R3 → ℝ) (x : R3) (hδ : 0 < δ) (hu : DifferentiableAt ℝ u x) :
    metricDifferentialNorm g (logProfile δ c p u) x =
      ((p : ℝ) * logSlope δ (u x)) * metricDifferentialNorm g u x := by
  let a : ℝ := (p : ℝ) * logSlope δ (u x)
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (u x) hδ).le
  have hg : gradient (logProfile δ c p u) x = a • gradient u x := by
    simp only [gradient, fderiv_logProfile δ c p u x hδ hu, profileDifferential]
    simp only [map_smul]
    rfl
  unfold metricDifferentialNorm
  rw [hg]
  have hq : coefficientQuadratic (inverseMetricOperator g) x (a • gradient u x) =
      a ^ 2 * coefficientQuadratic (inverseMetricOperator g) x (gradient u x) := by
    unfold coefficientQuadratic
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

lemma coordinateHessian_logProfile_metric_le (g : MatrixField) (hp : ∀ x, (g x).PosDef)
    (δ c C : ℝ) (p : ℕ) (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (x X : R3)
    (hδ : 0 < δ) (hC : 0 < C) (hb : metricDifferentialNorm g u x ≤ C)
    (hdepth : coordinateHessian u
      (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
        x V W) x X X ≤ -⟪metricOperatorField g x X, X⟫_ℝ) :
    coordinateHessian (logProfile δ c p u)
      (fun V W => coordinateConnectionField (inverseMetricOperator g) (metricOperatorField g)
        x V W) x X X ≤
      -(1 / C) * metricDifferentialNorm g (logProfile δ c p u) x *
        ⟪metricOperatorField g x X, X⟫_ℝ := by
  have hd := hu.differentiable (by simp)
  have hD := (contDiff_infty_iff_fderiv.mp hu).2
  rw [coordinateHessian_logProfile δ c p u _ x _ _ hδ (hd x).hasFDerivAt
    (hD.differentiable (by simp) x).hasFDerivAt (Filter.Eventually.of_forall hd)]
  have ha : 0 ≤ (p : ℝ) * logSlope δ (u x) :=
    mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (u x) hδ).le
  have hfirst := mul_le_mul_of_nonneg_left hdepth ha
  have hsecond : (p : ℝ) * logSlopeDerivative δ (u x) *
      (fderiv ℝ u x X) * (fderiv ℝ u x X) ≤ 0 := by
    have h := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p)
        (logSlopeDerivative_neg δ (u x) hδ).le) (sq_nonneg (fderiv ℝ u x X))
    convert h using 1 <;> ring
  have hform : profileHessianForm δ (u x) p
      (coordinateHessian u (fun V W => coordinateConnectionField (inverseMetricOperator g)
        (metricOperatorField g) x V W) x) (fderiv ℝ u x) X X ≤
      -((p : ℝ) * logSlope δ (u x)) * ⟪metricOperatorField g x X, X⟫_ℝ := by
    unfold profileHessianForm
    nlinarith
  have hm : 0 ≤ ⟪metricOperatorField g x X, X⟫_ℝ := by
    rw [metricOperatorField_inner_eq_quadratic, Matrix.toQuadraticForm'_apply]
    exact (hp x).posSemidef.dotProduct_mulVec_nonneg (X : Fin 3 → ℝ)
  have hab := mul_le_mul_of_nonneg_left hb ha
  have hratio : (1 / C) * (((p : ℝ) * logSlope δ (u x)) * metricDifferentialNorm g u x) ≤
      (p : ℝ) * logSlope δ (u x) := by
    have hr := (div_le_iff₀ hC).mpr hab
    convert hr using 1 <;> ring
  rw [metricDifferentialNorm_logProfile g δ c p u x hδ (hd x)]
  apply hform.trans
  have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hratio hm)
  convert hneg using 1 <;> ring

lemma exists_referenceDepth_metricNorm_bounds_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ m C T : ℝ, 0 < m ∧ 0 < C ∧ ∀ x ∈ K,
      m ≤ metricDifferentialNorm (referenceMetric g L) (referenceDepth L) x ∧
      metricDifferentialNorm (referenceMetric g L) (referenceDepth L) x ≤ C ∧
      referenceDepth L x ≤ T := by
  have hb := continuous_metricDifferentialNorm _ (referenceMetric_smooth_entries g hg L)
    (referenceMetric_posDef g hg L) _ (contDiff_referenceDepth L)
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' hb.continuousOn (a := (0 : ℝ))
    (fun x _ => metricDifferentialNorm_pos _ (referenceMetric_posDef g hg L) _ x
      (fderiv_referenceDepth_ne_zero L (ne_of_gt hL) x))
  obtain ⟨A, hmax⟩ := hK.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨T, ht⟩ := hK.exists_bound_of_continuousOn (contDiff_referenceDepth L).continuous.continuousOn
  refine ⟨m, max A 0 + 1, T, hm, by positivity, ?_⟩
  intro x hx
  refine ⟨hmin x hx, ?_, (le_abs_self _).trans (ht x hx)⟩
  have h := (le_abs_self _).trans (hmax x hx)
  exact h.trans (by linarith [le_max_left A 0])

theorem exists_referenceProfile_metric_bounds_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c0 c1 : ℝ, 0 < L ∧ 0 < c0 ∧ 0 < c1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, ∀ p : ℕ, ∀ x ∈ K,
        c0 * (p : ℝ) ≤ metricDifferentialNorm (referenceMetric g L)
          (logProfile δ c p (referenceDepth L)) x ∧
        ∀ X : R3, coordinateHessian (logProfile δ c p (referenceDepth L))
          (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric g L))
            (metricOperatorField (referenceMetric g L)) x V W) x X X ≤
          -c1 * metricDifferentialNorm (referenceMetric g L)
            (logProfile δ c p (referenceDepth L)) x *
              ⟪metricOperatorField (referenceMetric g L) x X, X⟫_ℝ := by
  obtain ⟨L, hL, hdepth⟩ := exists_referenceDepth_strict_hessian_bound_on_compact g hg K hK
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_referenceDepth_metricNorm_bounds_on_compact g hg L hL K hK
  let a : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha : 0 < a := by
    dsimp [a]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  refine ⟨L, a * m, 1 / C, hL, mul_pos ha hm, one_div_pos.mpr hC, ?_⟩
  intro δ hδ hδ1 c p x hx
  obtain ⟨hmin, hmax, ht⟩ := hbounds x hx
  constructor
  · rw [metricDifferentialNorm_logProfile _ δ c p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have hs : a ≤ logSlope δ (referenceDepth L x) := logSlope_uniform_lower_bound δ _ T hδ hδ1 ht
    have h1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg p)
    have h2 := mul_le_mul h1 hmin hm.le
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ _ hδ).le)
    convert h2 using 1 <;> ring
  · intro X
    exact coordinateHessian_logProfile_metric_le _ (referenceMetric_posDef g hg L) δ c C p _
      (contDiff_referenceDepth L) x X hδ hC hmax (hdepth x hx X)

end OAI.AnisotropicCalderon.ConformalDepth
