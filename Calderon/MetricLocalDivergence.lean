import Calderon.MetricHessianDivergence
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open scoped Matrix.Norms.Operator InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.MetricVolume

lemma metricDerivative_symmetric_local (g : MatrixField) (x V : R3)
    (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian) (i j : Fin 3) :
    fderiv ℝ (fun y => g y i j) x V = fderiv ℝ (fun y => g y j i) x V := by
  have he : (fun y => g y i j) =ᶠ[𝓝 x] (fun y => g y j i) := by
    filter_upwards [hs] with y hy
    simpa using (hy.apply j i)
  rw [he.fderiv_eq]

lemma densityInverse_connection_contraction_local (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian) (j : Fin 3) :
    (∑ i : Fin 3, fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x (coordinateVector i)) =
      -vol g x * ∑ a : Fin 3, ∑ b : Fin 3,
        (g x)⁻¹ a b * metricChristoffel g x a b j := by
  simp_rw [fderiv_densityInverse_entry g x _ hg hp, metricChristoffel_eq g x hg]
  exact symmetric_koszul_contraction (fun a b => ((g x)⁻¹ : Mat) a b)
    (fun i a b => fderiv ℝ (fun y => g y a b) x (coordinateVector i))
    (vol g x) (inverseMetric_symmetric g x hp)
    (fun i a b => metricDerivative_symmetric_local g x (coordinateVector i) hs a b) j

lemma densityWeightedDivergence_eq_metricHessian_trace_local (g : MatrixField) (f : R3 → ℝ)
    (x : R3) (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (g y).IsHermitian) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) x =
    vol g x * ∑ i : Fin 3, ∑ j : Fin 3, (g x)⁻¹ i j *
      RadiusProfile.coordinateHessian f
        (fun X Y => ConnectionError.coordinateConnectionField
          (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
          (MetricOperator.metricOperatorField g) x X Y) x (coordinateVector i) (coordinateVector j) := by
  have hH (i j : Fin 3) : RadiusProfile.coordinateHessian f
      (fun X Y => ConnectionError.coordinateConnectionField
        (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
        (MetricOperator.metricOperatorField g) x X Y) x (coordinateVector i) (coordinateVector j) =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) -
        ∑ k : Fin 3, metricChristoffel g x i j k * fderiv ℝ f x (coordinateVector k) := by
    unfold RadiusProfile.coordinateHessian
    rw [covector_coordinate_sum (fderiv ℝ f x)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    unfold metricChristoffel
    simp only [ConnectionError.coordinateConnectionField_apply,
      inverseMetricField_eq_matrix_inverse_of_posDef g x hp]
  unfold AngularPolynomial.densityWeightedDivergence
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial]
  change (∑ i : Fin 3, fderiv ℝ (fun y => vol g y *
    (MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) i) x (coordinateVector i)) = _
  simp_rw [derivative_density_gradient_entry g f x hg hp hf, hH]
  exact finite_divergence_trace
    (fun i j => fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x (coordinateVector i))
    (fun i j => ((g x)⁻¹ : Mat) i j)
    (fun i j => fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j))
    (metricChristoffel g x) (fun j => fderiv ℝ f x (coordinateVector j)) (vol g x)
    (densityInverse_connection_contraction_local g x hg hp hs)


lemma densityWeightedDivergence_eq_metricHessian_trace_on_open
    (g : MatrixField) (f : R3 → ℝ) (Y : Set R3) (hY : IsOpen Y) (x : R3) (hx : x ∈ Y)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y ∈ Y, (g y).PosDef) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (vol g) (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) x =
    vol g x * ∑ i : Fin 3, ∑ j : Fin 3, (g x)⁻¹ i j *
      RadiusProfile.coordinateHessian f
        (fun X Y => ConnectionError.coordinateConnectionField
          (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g))
          (MetricOperator.metricOperatorField g) x X Y) x (coordinateVector i) (coordinateVector j) := by
  apply densityWeightedDivergence_eq_metricHessian_trace_local g f x hg (hp x hx) _ hf
  filter_upwards [hY.mem_nhds hx] with y hy
  exact (hp y hy).isHermitian

end OAI.AnisotropicCalderon.MetricVolume
