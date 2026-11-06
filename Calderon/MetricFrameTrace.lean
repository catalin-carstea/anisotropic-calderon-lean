import Calderon.FischerDensityIntegration
import Calderon.MetricHessianQuadratic
import Calderon.ReferenceCovariantJets

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon.MetricFrameTrace
open RadiusProfile ConformalDepth MetricOperator MetricVolume AngularPolynomial
  FrameCurvaturePolynomial FischerDensityIntegration SmoothMetricFrame ReferenceDensityBounds

lemma matrixOperator_apply_inverse (M : Mat) (hM : M.PosDef) (v : R3) :
    matrixOperatorMap M (matrixOperatorMap M⁻¹ v) = v := by
  have h : matrixOperatorAlgEquiv M * matrixOperatorAlgEquiv M⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM.det_pos.ne'), map_one]
  exact congrArg (fun A : R3 →L[ℝ] R3 => A v) h

lemma inverseMatrix_metricFrame_sum (M : Mat) (hM : M.PosDef) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (matrixOperatorMap M) e) (v : R3) :
    matrixOperatorMap M⁻¹ v = ∑ i : Fin 3, ⟪v,e i⟫_ℝ • e i := by
  have h := metricFrame_sum_coordinates (matrixOperatorMap M) e he (matrixOperatorMap M⁻¹ v)
  rw [matrixOperator_apply_inverse M hM] at h
  exact h.symm

lemma inverseMatrix_entry_eq_metricFrame_sum (M : Mat) (hM : M.PosDef) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (matrixOperatorMap M) e) (i j : Fin 3) :
    M⁻¹ i j = ∑ a : Fin 3, (e a) i * (e a) j := by
  have h := congrArg (fun v : R3 => v i)
    (inverseMatrix_metricFrame_sum M hM e he (coordinateVector j))
  simpa [matrixOperator_coordinate, coordinateVector, PiLp.single_apply, mul_comm,
    EuclideanSpace.inner_single_left] using h

def metricFrameGradient (e : R3 → Fin 3 → R3) (f : R3 → ℝ) (x : R3) : R3 :=
  ∑ i : Fin 3, fderiv ℝ f x (e x i) • e x i

lemma metricFrameGradient_eq_inverse_gradient (g : MatrixField) (e : R3 → Fin 3 → R3)
    (f : R3 → ℝ) (x : R3) (hp : (g x).PosDef)
    (he : IsMetricOrthonormalFrame (metricOperatorField g x) (e x)) :
    metricFrameGradient e f x = matrixOperatorMap ((g x)⁻¹) (gradient f x) := by
  rw [inverseMatrix_metricFrame_sum (g x) hp (e x) he]
  simp only [metricFrameGradient, inner_gradient_left]

lemma contDiff_metricFrameGradient (e : R3 → Fin 3 → R3) (f : R3 → ℝ)
    (he : ∀ i, ContDiff ℝ ∞ (fun x => e x i)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (metricFrameGradient e f) := by
  have hd := (contDiff_infty_iff_fderiv.mp hf).2
  exact ContDiff.sum (fun i _ => (hd.clm_apply (he i)).smul (he i))

lemma bilinear_metricFrame_trace (M : Mat) (hM : M.PosDef) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (matrixOperatorMap M) e)
    (B : R3 →L[ℝ] R3 →L[ℝ] ℝ) :
    (∑ a : Fin 3, B (e a) (e a)) =
      ∑ i : Fin 3, ∑ j : Fin 3, M⁻¹ i j * B (coordinateVector i) (coordinateVector j) := by
  have hB (a : Fin 3) := bilinear_coordinate_sum B (e a) (e a)
  simp only [hB, inverseMatrix_entry_eq_metricFrame_sum M hM e he, Fin.sum_univ_three]
  ring

lemma weightedCoordinateDivergence_eq_densityWeightedDivergence (rho : R3 → ℝ)
    (V : R3 → R3) (x : R3) :
    weightedCoordinateDivergence rho V x =
      AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) rho V x := by
  simp only [weightedCoordinateDivergence, AngularPolynomial.densityWeightedDivergence,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul, conj_trivial,
    BaseDensityAdjoint.directionalDeriv, coordinateDirection]

theorem weightedCoordinateDivergence_metricFrameGradient_eq_hessian_trace
    (g : MatrixField) (e : R3 → Fin 3 → R3) (f : R3 → ℝ) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef)
    (he : ∀ y, IsMetricOrthonormalFrame (metricOperatorField g y) (e y))
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    weightedCoordinateDivergence (vol g) (metricFrameGradient e f) x =
      vol g x * ∑ a : Fin 3, coordinateHessian f
        (fun X Y => ConnectionError.coordinateConnectionField
          (ConnectionError.inverseMetricField (metricOperatorField g)) (metricOperatorField g) x X Y)
        x (e x a) (e x a) := by
  have hG : metricFrameGradient e f =
      fun y => matrixOperatorMap ((g y)⁻¹) (gradient f y) :=
    funext (fun y => metricFrameGradient_eq_inverse_gradient g e f y (hp y) (he y))
  rw [hG, weightedCoordinateDivergence_eq_densityWeightedDivergence,
    densityWeightedDivergence_eq_metricHessian_trace g f x hg hp hf]
  have hT := bilinear_metricFrame_trace (g x) (hp x) (e x) (he x)
    (MetricVolume.coordinateHessianBilinear f
      (ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (metricOperatorField g)) (metricOperatorField g) x) x)
  simp only [MetricVolume.coordinateHessianBilinear_apply] at hT
  rw [hT]

theorem reference_weightedCoordinateDivergence_metricFrameGradient_eq_hessian_trace
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y))
      (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f) x =
    referenceDensityFamily g L (lam,x) * ∑ a : Fin 3,
      coordinateHessian f (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) a) := by
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
  exact weightedCoordinateDivergence_metricFrameGradient_eq_hessian_trace
    (referenceMetric (dilatedMetric g lam) L) _ f x
    (fun i j => (hs i j).differentiable (by simp) x) hpos
    (fun y => referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,y))
    ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp) x)

end OAI.AnisotropicCalderon.MetricFrameTrace
