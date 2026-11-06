import Calderon.MetricDensityConnection
import Calderon.AngularEuclideanDensity
import Calderon.ProfileChain

noncomputable section
open scoped Matrix.Norms.Operator InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MetricVolume

lemma inverseMetricField_eq_matrix_inverse_of_posDef (g : MatrixField) (x : R3)
    (hp : (g x).PosDef) :
    ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) x =
      MetricOperator.matrixOperatorMap ((g x)⁻¹) := by
  obtain ⟨u, hu⟩ := hp.isUnit
  change Ring.inverse (MetricOperator.matrixOperatorAlgEquiv (g x)) =
    MetricOperator.matrixOperatorAlgEquiv ((g x)⁻¹)
  rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  change Ring.inverse ((Units.map MetricOperator.matrixOperatorAlgEquiv.toMonoidHom u).val) =
    ((Units.map MetricOperator.matrixOperatorAlgEquiv.toMonoidHom u)⁻¹).val
  rw [Ring.inverse_unit]

lemma gradient_coordinate (f : R3 → ℝ) (x : R3) (i : Fin 3) :
    (gradient f x) i = fderiv ℝ f x (coordinateVector i) := by
  rw [← inner_gradient_left]
  simp only [coordinateVector, EuclideanSpace.inner_single_right, one_mul, conj_trivial]

lemma covector_coordinate_sum (F : R3 →L[ℝ] ℝ) (V : R3) :
    F V = ∑ i : Fin 3, V i * F (coordinateVector i) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr V]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul, coordinateVector]

lemma derivative_covector_entry (f : R3 → ℝ) (x V : R3)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x V =
      fderiv ℝ (fderiv ℝ f) x V (coordinateVector j) := by
  rw [fderiv_clm_apply hf (differentiableAt_const (coordinateVector j))]
  simp

lemma derivative_density_gradient_entry (g : MatrixField) (f : R3 → ℝ) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (hp : (g x).PosDef)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (i : Fin 3) :
    fderiv ℝ (fun y => vol g y *
      (MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) i) x (coordinateVector i) =
      ∑ j : Fin 3, (
        fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x (coordinateVector i) *
          fderiv ℝ f x (coordinateVector j) +
        vol g x * (g x)⁻¹ i j *
          fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j)) := by
  have he : (fun y => vol g y *
      (MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) i) =
    (fun y => ∑ j : Fin 3, (vol g y * (g y)⁻¹ i j) *
      fderiv ℝ f y (coordinateVector j)) := by
    funext y
    simp_rw [matrixOperator_coordinate, gradient_coordinate, Finset.mul_sum, mul_assoc]
  have hv : DifferentiableAt ℝ (vol g) x :=
    ((hasFDerivAt_metric_determinant g x hg hp).sqrt hp.det_pos.ne').differentiableAt
  have hi (j : Fin 3) : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x := by
    let E : Mat →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)).differentiableAt
  have hf' (j : Fin 3) : DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (coordinateVector j)) x :=
    hf.clm_apply (differentiableAt_const (coordinateVector j))
  rw [he, fderiv_fun_sum (u := Finset.univ)
    (A := fun j y => (vol g y * (g y)⁻¹ i j) * fderiv ℝ f y (coordinateVector j))
    (fun j _ => (hv.mul (hi j)).mul (hf' j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (c := fun y => vol g y * ((g y)⁻¹ : Mat) i j)
    (d := fun y => fderiv ℝ f y (coordinateVector j)) (hv.mul (hi j)) (hf' j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [derivative_covector_entry f x _ hf j]
  ring

lemma finite_divergence_trace (A Q H : Fin 3 → Fin 3 → ℝ)
    (G : Fin 3 → Fin 3 → Fin 3 → ℝ) (F : Fin 3 → ℝ) (rho : ℝ)
    (hA : ∀ j, (∑ i : Fin 3, A i j) = -rho * ∑ a : Fin 3, ∑ b : Fin 3, Q a b * G a b j) :
    (∑ i : Fin 3, ∑ j : Fin 3, (A i j * F j + rho * Q i j * H i j)) =
      rho * ∑ i : Fin 3, ∑ j : Fin 3, Q i j * (H i j - ∑ k : Fin 3, G i j k * F k) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => A i j * F j)]
  simp_rw [← Finset.sum_mul, hA]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

lemma densityWeightedDivergence_eq_metricHessian_trace (g : MatrixField) (f : R3 → ℝ)
    (x : R3) (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : ∀ y, (g y).PosDef) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
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
      inverseMetricField_eq_matrix_inverse_of_posDef g x (hp x)]
  unfold AngularPolynomial.densityWeightedDivergence
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial]
  change (∑ i : Fin 3, fderiv ℝ (fun y => vol g y *
    (MetricOperator.matrixOperatorMap ((g y)⁻¹) (gradient f y)) i) x (coordinateVector i)) = _
  simp_rw [derivative_density_gradient_entry g f x hg (hp x) hf, hH]
  exact finite_divergence_trace
    (fun i j => fderiv ℝ (fun y => vol g y * (g y)⁻¹ i j) x (coordinateVector i))
    (fun i j => ((g x)⁻¹ : Mat) i j)
    (fun i j => fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j))
    (metricChristoffel g x) (fun j => fderiv ℝ f x (coordinateVector j)) (vol g x)
    (densityInverse_connection_contraction g x hg hp)

end OAI.AnisotropicCalderon.MetricVolume
