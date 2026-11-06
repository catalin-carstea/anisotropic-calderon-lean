import Calderon.PositiveMetricDensity
import Calderon.DepthChain

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

/-- The polynomial t₀ of the selected three-dimensional coordinate cylinder. -/
def referenceCoordinateDepth (x : R3) : ℝ := x 2 + x 0 ^ 2 + x 1 ^ 2

lemma contDiff_referenceCoordinateDepth : ContDiff ℝ ∞ referenceCoordinateDepth :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff.add
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.pow 2)).add
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.pow 2)

lemma hasFDerivAt_referenceCoordinateDepth (x : R3) :
    HasFDerivAt referenceCoordinateDepth
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) +
        (2 * x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) +
        (2 * x 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)) x := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := x)
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := x)
  convert (h2.add (h0.mul h0)).add (h1.mul h1) using 1
  · funext y
    simp only [referenceCoordinateDepth, pow_two]
    rfl
  · ext V
    simp only [add_apply, smul_apply, smul_eq_mul]
    change V 2 + (2 * x 0) * V 0 + (2 * x 1) * V 1 =
      V 2 + (x 0 * V 0 + x 0 * V 0) + (x 1 * V 1 + x 1 * V 1)
    ring

lemma fderiv_referenceCoordinateDepth_normal (x : R3) :
    fderiv ℝ referenceCoordinateDepth x (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = 1 := by
  rw [(hasFDerivAt_referenceCoordinateDepth x).fderiv]
  simp [EuclideanSpace.proj, PiLp.proj, PiLp.projₗ]

lemma fderiv_referenceCoordinateDepth_ne_zero (x : R3) :
    fderiv ℝ referenceCoordinateDepth x ≠ 0 := by
  intro h
  have hn := fderiv_referenceCoordinateDepth_normal x
  rw [h] at hn
  simp at hn

/-- The selected reference gamma, without an exterior-admissibility claim. -/
def referenceMetric (g : MatrixField) (L : ℝ) : MatrixField :=
  EnergyBridge.conformalMatrix g (fun x => -L * referenceCoordinateDepth x)

lemma referenceMetric_smooth_entries (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i j : Fin 3) : ContDiff ℝ ∞ (fun x => referenceMetric g L x i j) :=
  EnergyBridge.conformalMatrix_smooth_entries g _ hg.smooth
    (contDiff_const.mul contDiff_referenceCoordinateDepth) i j

lemma referenceMetric_posDef (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (x : R3) : (referenceMetric g L x).PosDef :=
  EnergyBridge.conformalMatrix_posDef g _ hg.posDef x

lemma referenceMetric_operator_eq (g : MatrixField) (L : ℝ) (x : R3) :
    metricOperatorField (referenceMetric g L) x =
      Real.exp (-2 * L * referenceCoordinateDepth x) • metricOperatorField g x := by
  change matrixOperatorMap (Real.exp (2 * (-L * referenceCoordinateDepth x)) • g x) = _
  rw [map_smul]
  congr 1
  congr 1
  ring

/-- The transformed depth t, kept distinct from its polynomial input t₀. -/
def referenceDepth (L : ℝ) : R3 → ℝ :=
  depthFunction L (1 / 8) referenceCoordinateDepth

lemma contDiff_referenceDepth (L : ℝ) : ContDiff ℝ ∞ (referenceDepth L) := by
  unfold referenceDepth depthFunction depthPrimitive
  exact (contDiff_const.sub
    ((contDiff_const.mul contDiff_referenceCoordinateDepth).exp)).div_const _

lemma hasFDerivAt_referenceDepth (L : ℝ) (hL : L ≠ 0) (x : R3) :
    HasFDerivAt (referenceDepth L)
      (Real.exp (-2 * L * referenceCoordinateDepth x) •
        fderiv ℝ referenceCoordinateDepth x) x :=
  hasFDerivAt_depthFunction L (1 / 8) referenceCoordinateDepth x _ hL
    (contDiff_referenceCoordinateDepth.differentiable (by simp) x).hasFDerivAt

lemma referenceDepth_zero_neg (L : ℝ) (hL : 0 < L) : referenceDepth L 0 < 0 := by
  change depthPrimitive L (1 / 8) (referenceCoordinateDepth 0) < 0
  simp only [referenceCoordinateDepth, PiLp.zero_apply, zero_pow (by decide : 2 ≠ 0),
    add_zero]
  exact depthPrimitive_zero_neg L (1 / 8) hL (by norm_num)

lemma fderiv_referenceDepth_ne_zero (L : ℝ) (hL : L ≠ 0) (x : R3) :
    fderiv ℝ (referenceDepth L) x ≠ 0 := by
  intro h
  have hn := congrArg
    (fun T : R3 →L[ℝ] ℝ => T (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))) h
  rw [(hasFDerivAt_referenceDepth L hL x).fderiv] at hn
  simp only [smul_apply, smul_eq_mul, fderiv_referenceCoordinateDepth_normal, mul_one,
    zero_apply] at hn
  exact Real.exp_ne_zero _ hn

lemma fderiv_referenceMetricOperator (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (x : R3) :
    fderiv ℝ (metricOperatorField (referenceMetric g L)) x =
      conformalMetricDerivative (Real.exp (-2 * L * referenceCoordinateDepth x)) L
        (metricOperatorField g x) (fderiv ℝ (metricOperatorField g) x)
        (fderiv ℝ referenceCoordinateDepth x) := by
  have he : metricOperatorField (referenceMetric g L) =
      fun y => Real.exp (-2 * L * referenceCoordinateDepth y) • metricOperatorField g y :=
    funext (referenceMetric_operator_eq g L)
  rw [he]
  exact (hasFDerivAt_conformalMetric L referenceCoordinateDepth (metricOperatorField g) x _ _
    (contDiff_referenceCoordinateDepth.differentiable (by simp) x).hasFDerivAt
    ((contDiff_metricOperatorField g hg).differentiable (by simp) x).hasFDerivAt).fderiv

lemma referenceMetric_connection (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (x X Y : R3) :
    coordinateConnectionField (inverseMetricOperator (referenceMetric g L))
        (metricOperatorField (referenceMetric g L)) x X Y =
      conformalConnection L (inverseMetricOperator g x) (metricOperatorField g x)
        (fderiv ℝ (metricOperatorField g) x) (fderiv ℝ referenceCoordinateDepth x) X Y := by
  have hi : inverseMetricOperator (referenceMetric g L) x =
      (Real.exp (-2 * L * referenceCoordinateDepth x))⁻¹ • inverseMetricOperator g x := by
    rw [referenceMetric, inverseMetricOperator_conformalMatrix g _ hg.posDef]
    congr 1
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [coordinateConnectionField_apply, hi, fderiv_referenceMetricOperator g hg]
  exact coordinateConnection_conformal _ L _ _ _ _ (Real.exp_ne_zero _)
    (fun V => inverseMetricField_apply_metric _ (isUnit_metricOperatorField g hg) x V)
    (fun V => metric_apply_inverseMetricField _ (isUnit_metricOperatorField g hg) x V)
    (metricOperatorField_symmetric g hg x) X Y

lemma referenceDepth_coordinateHessian (g : MatrixField) (hg : IsAdmissibleMetric g)
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
  have hi : inverseMetricOperator (referenceMetric g L) x =
      (Real.exp (-2 * L * referenceCoordinateDepth x))⁻¹ • inverseMetricOperator g x := by
    rw [referenceMetric, inverseMetricOperator_conformalMatrix g _ hg.posDef]
    congr 1
    rw [← Real.exp_neg]
    congr 1
    ring
  have hsecond := (contDiff_infty_iff_fderiv.mp contDiff_referenceCoordinateDepth).2
  have ht := (contDiff_referenceCoordinateDepth.differentiable (by simp) x).hasFDerivAt
  have hH := (hsecond.differentiable (by simp) x).hasFDerivAt
  have hn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ referenceCoordinateDepth y :=
    Filter.Eventually.of_forall (contDiff_referenceCoordinateDepth.differentiable (by simp))
  simp only [coordinateConnectionField_apply]
  change coordinateHessian (depthFunction L (1 / 8) referenceCoordinateDepth)
    (coordinateConnection (inverseMetricOperator (referenceMetric g L) x)
      (fderiv ℝ (metricOperatorField (referenceMetric g L)) x)) x X Y = _
  rw [hi, fderiv_referenceMetricOperator g hg]
  exact coordinateHessian_depthFunction L (1 / 8) referenceCoordinateDepth x _ _ _ _ _ hL ht hH hn
    (fun V => inverseMetricField_apply_metric _ (isUnit_metricOperatorField g hg) x V)
    (fun V => metric_apply_inverseMetricField _ (isUnit_metricOperatorField g hg) x V)
    (metricOperatorField_symmetric g hg x) X Y

end OAI.AnisotropicCalderon.ConformalDepth
