import Calderon.MetricLocalDivergence
import Calderon.MetricNegativeTrace

noncomputable section
open scoped Matrix.Norms.Operator Gradient Topology
namespace OAI.AnisotropicCalderon.MetricVolume

def metricHessianMatrix (g : MatrixField) (f : R3 → ℝ) (x : R3) : Mat :=
  fun i j => RadiusProfile.coordinateHessian f
    (fun X Y => ConnectionError.coordinateConnectionField
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
      (MetricOperator.metricOperatorField g) x X Y) x (coordinateVector i) (coordinateVector j)

lemma densityWeightedDivergence_le_of_negative_metricHessian_local
    (g : MatrixField) (f : R3 → ℝ) (x : R3) (a : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hH : (-metricHessianMatrix g f x - a • g x).PosSemidef) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) x ≤
      -3 * vol g x * a := by
  rw [densityWeightedDivergence_eq_metricHessian_trace_local g f x hg hp hs hf]
  have h := mul_le_mul_of_nonneg_left
    (inverse_metric_negative_coordinate_le (g x) (metricHessianMatrix g f x) a hp hH)
    (Real.sqrt_nonneg ((g x).det))
  change vol g x * (∑ i : Fin 3, ∑ j : Fin 3, (g x)⁻¹ i j *
    metricHessianMatrix g f x i j) ≤ vol g x * (-3 * a) at h
  simpa only [metricHessianMatrix, mul_left_comm, mul_assoc] using h

lemma densityWeightedDivergence_le_of_negative_metricHessian_on_open
    (g : MatrixField) (f : R3 → ℝ) (Y : Set R3) (hY : IsOpen Y)
    (x : R3) (hx : x ∈ Y) (a : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y ∈ Y, (g y).PosDef) (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hH : (-metricHessianMatrix g f x - a • g x).PosSemidef) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) x ≤
      -3 * vol g x * a := by
  apply densityWeightedDivergence_le_of_negative_metricHessian_local g f x a hg (hp x hx) _ hf hH
  filter_upwards [hY.mem_nhds hx] with y hy
  exact (hp y hy).isHermitian

end OAI.AnisotropicCalderon.MetricVolume
