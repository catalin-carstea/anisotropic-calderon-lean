import Calderon.MetricFrameTrace
import Calderon.MetricDensityConnection
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon.MetricFrameDivergence
open RadiusProfile ConformalDepth MetricOperator MetricVolume AngularPolynomial
  FrameCurvaturePolynomial FischerDensityIntegration SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds BaseDensityAdjoint MetricFrameTrace

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField

lemma metricFrame_endomorphism_trace (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (A : R3 →L[ℝ] R3) :
    (∑ a : Fin 3, ⟪M (A (e a)),e a⟫_ℝ) =
      ∑ i : Fin 3, (A (coordinateVector i)) i := by
  have h := congrArg (fun T : (R3 →ₗ[ℝ] R3) →ₗ[ℝ] ℝ => T A.toLinearMap)
    (LinearMap.traceAux_eq ℝ (metricFrameBasis M e he) (PiLp.basisFun 2 ℝ (Fin 3)))
  simpa only [LinearMap.traceAux_def,Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,
    metricFrameBasis_apply,metricFrameBasis_repr,PiLp.basisFun_apply,
    PiLp.basisFun_repr,coordinateVector,EuclideanSpace.single,ContinuousLinearMap.coe_coe] using h

lemma symmetric_christoffel_trace (Q : Fin 3 → Fin 3 → ℝ)
    (D : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hQ : ∀ a b, Q a b = Q b a) (hD : ∀ i a b, D i a b = D i b a) (j : Fin 3) :
    (∑ i : Fin 3, (1/2 : ℝ) * ∑ c : Fin 3,
      Q i c * (D i c j + D j c i - D c j i)) =
      (1/2 : ℝ) * ∑ a : Fin 3, ∑ b : Fin 3, Q b a * D j a b := by
  fin_cases j <;> simp only [Fin.sum_univ_three]
  all_goals
    simp only [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 3) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin 3) = 2 from rfl]
    simp only [hQ 1 0,hQ 2 0,hQ 2 1,
      hD 0 1 0,hD 0 2 0,hD 0 2 1,
      hD 1 1 0,hD 1 2 0,hD 1 2 1,
      hD 2 1 0,hD 2 2 0,hD 2 2 1]
    ring

lemma fderiv_vol_coordinate_eq_christoffel_trace (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef) (j : Fin 3) :
    fderiv ℝ (vol g) x (coordinateVector j) = vol g x * ∑ i : Fin 3, metricChristoffel g x i j i := by
  rw [fderiv_vol_apply_entries g x _ hg (hp x)]
  simp_rw [metricChristoffel_eq g x hg]
  rw [symmetric_christoffel_trace _ _ (inverseMetric_symmetric g x (hp x))
    (fun i a b => metricDerivative_symmetric g x (coordinateVector i) hp a b)]
  ring

lemma fderiv_vol_eq_connection_trace (g : MatrixField) (x V : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef) :
    fderiv ℝ (vol g) x V = vol g x * ∑ i : Fin 3,
      (ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (metricOperatorField g)) (metricOperatorField g) x
        (coordinateVector i) V) i := by
  have hV : V = ∑ j : Fin 3, V j • coordinateVector j := by
    simpa only [coordinateVector,coordinateDirection,PiLp.basisFun_apply] using vector_eq_sum_coordinateDirection V
  have he : ConnectionError.inverseMetricField (metricOperatorField g) =
      fun y => matrixOperatorMap ((g y)⁻¹) :=
    funext (fun y => inverseMetricField_eq_matrix_inverse_of_posDef g y (hp y))
  rw [he]
  conv_lhs => rw [hV]
  simp only [map_sum,map_smul,smul_eq_mul,fderiv_vol_coordinate_eq_christoffel_trace g x hg hp]
  conv_rhs => arg 2; arg 2; intro i; rw [hV]
  simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,metricChristoffel,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

lemma fderiv_vectorComponent (V : R3 → R3) (x X : R3)
    (hV : DifferentiableAt ℝ V x) (i : Fin 3) :
    fderiv ℝ (fun y => (V y) i) x X = (fderiv ℝ V x X) i := by
  have h := (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : R3 →L[ℝ] ℝ).hasFDerivAt.comp x hV.hasFDerivAt
  change HasFDerivAt (fun y => (V y) i) _ x at h
  rw [h.fderiv]
  rfl

lemma weightedCoordinateDivergence_eq_derivative_trace (rho : R3 → ℝ) (V : R3 → R3) (x : R3)
    (hr : DifferentiableAt ℝ rho x) (hV : DifferentiableAt ℝ V x) :
    weightedCoordinateDivergence rho V x =
      fderiv ℝ rho x (V x) + rho x * ∑ i : Fin 3, (fderiv ℝ V x (coordinateVector i)) i := by
  have hv (i : Fin 3) : DifferentiableAt ℝ (fun y => (V y) i) x :=
    ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : R3 →L[ℝ] ℝ).differentiableAt).comp x hV
  simp only [weightedCoordinateDivergence,directionalDeriv]
  simp_rw [fderiv_fun_mul hr (hv _)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    fderiv_vectorComponent V x _ hV,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [directionalDeriv_variable_eq_sum]
  simp only [directionalDeriv,coordinateDirection,coordinateVector,PiLp.basisFun_apply]
  rw [add_comm]

theorem weightedCoordinateDivergence_eq_metricFrame_trace
    (g : MatrixField) (e : Fin 3 → R3) (V : R3 → R3) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef)
    (he : IsMetricOrthonormalFrame (metricOperatorField g x) e)
    (hV : DifferentiableAt ℝ V x) :
    weightedCoordinateDivergence (vol g) V x = vol g x * ∑ a : Fin 3,
      ⟪metricOperatorField g x (fderiv ℝ V x (e a) +
        ConnectionError.coordinateConnectionField
          (ConnectionError.inverseMetricField (metricOperatorField g)) (metricOperatorField g) x (e a) (V x)),e a⟫_ℝ := by
  have hr : DifferentiableAt ℝ (vol g) x :=
    ((hasFDerivAt_metric_determinant g x hg (hp x)).sqrt (hp x).det_pos.ne').differentiableAt
  rw [weightedCoordinateDivergence_eq_derivative_trace _ _ x hr hV,
    fderiv_vol_eq_connection_trace g x (V x) hg hp]
  have ht := metricFrame_endomorphism_trace (metricOperatorField g x) e he
    (fderiv ℝ V x + (ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (metricOperatorField g)) (metricOperatorField g) x).flip (V x))
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.flip_apply,
    PiLp.add_apply,Finset.sum_add_distrib] at ht
  rw [ht]
  ring

theorem reference_weightedCoordinateDivergence_eq_metricFrame_trace
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V) (x : R3) :
    weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y)) V x =
    referenceDensityFamily g L (lam,x) * ∑ a : Fin 3,
      ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x
        (fderiv ℝ V x (referenceMetricGramFrame g L (lam,x) a) +
          referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) a) (V x)),
        referenceMetricGramFrame g L (lam,x) a⟫_ℝ := by
  have hpos : ∀ y, (referenceMetric (dilatedMetric g lam) L y).PosDef := by
    intro y
    exact EnergyBridge.conformalMatrix_posDef _ _ (fun z => hg.posDef (lam • z)) y
  have hs : ∀ i j, ContDiff ℝ ∞ (fun y => referenceMetric (dilatedMetric g lam) L y i j) := by
    intro i j
    exact EnergyBridge.conformalMatrix_smooth_entries _ _
      (fun i j => (hg.smooth i j).comp
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => lam)).smul
          (contDiff_id : ContDiff ℝ ∞ (fun y : R3 => y))))
      (contDiff_const.mul contDiff_referenceCoordinateDepth) i j
  have h := weightedCoordinateDivergence_eq_metricFrame_trace
    (referenceMetric (dilatedMetric g lam) L) _ V x
    (fun i j => (hs i j).differentiable (by simp) x) hpos
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))
    (hV.differentiable (by simp) x)
  have hInv : ConnectionError.inverseMetricField
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) =
      inverseMetricOperator (referenceMetric (dilatedMetric g lam) L) := by
    funext y
    rw [inverseMetricOperator_eq_matrix_inverse_of_posDef _ hpos]
    exact inverseMetricField_eq_matrix_inverse_of_posDef _ y (hpos y)
  rw [hInv] at h
  simpa only [referenceDensityFamily,referenceConnectionFamily] using h

theorem reference_weightedCoordinateDivergence_gramFrame
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (i : Fin 3) (x : R3) :
    weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y))
      (fun y => referenceMetricGramFrame g L (lam,y) i) x =
    referenceDensityFamily g L (lam,x) * ∑ a : Fin 3,
      referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) a) a i := by
  exact reference_weightedCoordinateDivergence_eq_metricFrame_trace g hg L lam _
    (contDiff_referenceMetricGramFrame_slice g hg L lam i) x

end OAI.AnisotropicCalderon.MetricFrameDivergence
