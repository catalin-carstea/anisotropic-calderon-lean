import Calderon.ActualNormalizedSecondMetricDrift
import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import Calderon.ConformalFluxDivergence

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondMetricDrift
open EnergyBridge ConnectionError MetricOperator MetricVolume
  AngularPolynomial ConformalDepth

theorem densityWeightedDivergence_eq_divCoeffGrad_principalCoefficient
    (g : MatrixField) (u : R3 → ℝ) (x : R3) :
    densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => matrixOperatorMap ((g y)⁻¹) (gradient u y)) x =
      divCoeffGrad (principalCoefficient g) u x := by
  unfold densityWeightedDivergence divCoeffGrad
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun f : R3 → ℝ => fderiv ℝ f x (EuclideanSpace.single i 1))
  funext z
  change vol g z * (∑ j : Fin 3, (g z)⁻¹ i j * (gradient u z) j) =
    ∑ j : Fin 3, (principalCoefficient g z) i j *
      fderiv ℝ u z (EuclideanSpace.single j 1)
  simp_rw [MetricVolume.gradient_coordinate]
  simp only [principalCoefficient, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    MetricVolume.coordinateVector, mul_assoc]

theorem coordinateFluxDivergence_metric_eq_divCoeffGrad
    (g : MatrixField) (u : R3 → ℝ) (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      divCoeffGrad (principalCoefficient g) u x := by
  unfold coordinateFluxDivergence divCoeffGrad
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun f : R3 → ℝ => fderiv ℝ f x (EuclideanSpace.single i 1))
  funext z
  change (∑ j : Fin 3, (principalCoefficient g z) i j * (gradient u z) j) =
    ∑ j : Fin 3, (principalCoefficient g z) i j *
      fderiv ℝ u z (EuclideanSpace.single j 1)
  simp_rw [MetricVolume.gradient_coordinate]
  rfl

theorem normalizedSecondLaplacian_eq_zero_iff_divCoeffGrad
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam : ℝ) (u : R3 → ℝ) (x : R3) :
    normalizedSecondLaplacian g1 g2 L lam u x = 0 ↔
      divCoeffGrad (principalCoefficient (fun y => g2 (lam • y))) u x = 0 := by
  have hs : normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) ≠ 0 :=
    (normalizedSecondLaplacianScalarJoint_pos g1 g2 hg1 hg2 L (lam,x)).ne'
  have hv : vol (dilatedMetric g2 lam) x ≠ 0 :=
    (vol_pos_of_posDef _ (dilatedMetric_posDef g2 hg2 lam) x).ne'
  unfold normalizedSecondLaplacian
  rw [densityWeightedDivergence_eq_divCoeffGrad_principalCoefficient]
  simp only [mul_eq_zero, hs, inv_ne_zero hv, false_or]
  rfl

end OAI.AnisotropicCalderon.ActualNormalizedSecondMetricDrift

