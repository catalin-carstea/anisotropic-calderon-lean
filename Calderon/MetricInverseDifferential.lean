import Calderon.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open scoped Matrix.Norms.Operator
namespace OAI.AnisotropicCalderon.MetricVolume

def inverseMatrixDerivative (M : Mat) : Mat →L[ℝ] Mat :=
  -ContinuousLinearMap.mulLeftRight ℝ Mat M⁻¹ M⁻¹

lemma inverseMatrixDerivative_apply (M H : Mat) :
    inverseMatrixDerivative M H = -(M⁻¹ * H * M⁻¹) := rfl

lemma hasFDerivAt_inverseMatrix_of_isUnit (M : Mat) (hM : IsUnit M) :
    HasFDerivAt (fun Y : Mat => Y⁻¹) (inverseMatrixDerivative M) M := by
  obtain ⟨u, hu⟩ := hM
  have hi : (↑u⁻¹ : Mat) = M⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have he : (Ring.inverse : Mat → Mat) = fun Y : Mat => Y⁻¹ := by
    funext Y
    exact (Matrix.nonsing_inv_eq_ringInverse Y).symm
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [he, hi, hu] at h
  exact h

lemma hasFDerivAt_inverseMetric_matrix (g : MatrixField) (x : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    HasFDerivAt (fun y => (g y)⁻¹)
      ((inverseMatrixDerivative (g x)).comp (matrixFieldDerivative g x)) x :=
  (hasFDerivAt_inverseMatrix_of_isUnit (g x) hp.isUnit).comp x
    (hasFDerivAt_matrixField_of_entries g x hg)

lemma fderiv_inverseMetric_matrix_apply (g : MatrixField) (x V : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) :
    fderiv ℝ (fun y => (g y)⁻¹) x V =
      -((g x)⁻¹ * matrixFieldDerivative g x V * (g x)⁻¹) := by
  rw [(hasFDerivAt_inverseMetric_matrix g x hg hp).fderiv]
  rfl

lemma fderiv_inverseMetric_entry_apply (g : MatrixField) (x V : R3)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (i j : Fin 3) :
    fderiv ℝ (fun y => (g y)⁻¹ i j) x V =
      -∑ a : Fin 3, ∑ b : Fin 3,
        (g x)⁻¹ i a * fderiv ℝ (fun y => g y a b) x V * (g x)⁻¹ b j := by
  let E : Mat →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have h := E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)
  change HasFDerivAt (fun y => (g y)⁻¹ i j)
    (E.comp ((inverseMatrixDerivative (g x)).comp (matrixFieldDerivative g x))) x at h
  rw [h.fderiv]
  change -((g x)⁻¹ * matrixFieldDerivative g x V * (g x)⁻¹) i j = _
  simp only [Matrix.mul_apply, matrixFieldDerivative_apply_entry,
    Matrix.neg_apply, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

end OAI.AnisotropicCalderon.MetricVolume
