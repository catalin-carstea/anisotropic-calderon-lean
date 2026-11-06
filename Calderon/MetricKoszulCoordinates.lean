import Calderon.MetricVolumeDifferential
import Calderon.MetricOperator

noncomputable section
open scoped Matrix.Norms.Operator InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricVolume

def coordinateVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

def matrixOperatorMapOp : Mat →L[ℝ] R3 →L[ℝ] R3 :=
  MetricOperator.matrixOperatorAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

lemma matrixOperatorMapOp_apply (M : Mat) (V : R3) :
    matrixOperatorMapOp M V = M.toEuclideanLin V := rfl

lemma matrixOperator_coordinate (M : Mat) (V : R3) (i : Fin 3) :
    (MetricOperator.matrixOperatorMap M V) i = ∑ j : Fin 3, M i j * V j := rfl

lemma matrixOperator_basis_inner (M : Mat) (i j : Fin 3) :
    ⟪MetricOperator.matrixOperatorMap M (coordinateVector j), coordinateVector i⟫_ℝ = M i j := by
  simp only [coordinateVector, EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  rw [matrixOperator_coordinate]
  simp [PiLp.single_apply]

lemma hasFDerivAt_actualMetricOperator (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    HasFDerivAt (MetricOperator.metricOperatorField g)
      (matrixOperatorMapOp.comp (matrixFieldDerivative g x)) x := by
  exact matrixOperatorMapOp.hasFDerivAt.comp x (hasFDerivAt_matrixField_of_entries g x hg)

lemma metricOperator_derivative_entry (g : MatrixField) (x V : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (i j : Fin 3) :
    ⟪fderiv ℝ (MetricOperator.metricOperatorField g) x V (coordinateVector j),
      coordinateVector i⟫_ℝ = fderiv ℝ (fun y => g y i j) x V := by
  rw [(hasFDerivAt_actualMetricOperator g x hg).fderiv]
  change ⟪MetricOperator.matrixOperatorMap (matrixFieldDerivative g x V)
      (coordinateVector j), coordinateVector i⟫_ℝ = _
  rw [matrixOperator_basis_inner, matrixFieldDerivative_apply_entry]

lemma riesz_coordinate (F : R3 →L[ℝ] ℝ) (i : Fin 3) :
    ((InnerProductSpace.toDual ℝ R3).symm F) i = F (coordinateVector i) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := coordinateVector i) (y := F)
  rw [← h]
  simp only [coordinateVector, EuclideanSpace.inner_single_right, one_mul, conj_trivial]

def metricChristoffel (g : MatrixField) (x : R3) (i j k : Fin 3) : ℝ :=
  (ConnectionError.coordinateConnectionField
    (fun y => MetricOperator.matrixOperatorMap ((g y)⁻¹))
    (MetricOperator.metricOperatorField g) x (coordinateVector i) (coordinateVector j)) k

lemma metricChristoffel_eq (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (i j k : Fin 3) :
    metricChristoffel g x i j k = (1 / 2 : ℝ) * ∑ c : Fin 3,
      (g x)⁻¹ k c * (fderiv ℝ (fun y => g y c j) x (coordinateVector i) +
        fderiv ℝ (fun y => g y c i) x (coordinateVector j) -
        fderiv ℝ (fun y => g y j i) x (coordinateVector c)) := by
  unfold metricChristoffel
  rw [ConnectionError.coordinateConnectionField_apply]
  simp only [ConnectionError.coordinateConnection, PiLp.smul_apply, smul_eq_mul]
  rw [matrixOperator_coordinate]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [riesz_coordinate, ConnectionError.koszulFunctional_apply]
  rw [metricOperator_derivative_entry g x (coordinateVector i) hg c j,
    metricOperator_derivative_entry g x (coordinateVector j) hg c i,
    metricOperator_derivative_entry g x (coordinateVector c) hg j i]

end OAI.AnisotropicCalderon.MetricVolume
