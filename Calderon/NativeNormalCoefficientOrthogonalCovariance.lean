import Calderon.NativeOrthogonalCoefficientEnergyCovariance
import Calderon.NativeBoundaryCoefficientFamilies

/-! Expanded first in EXPANSION-actual-rotation-normal-multiplier-inverse-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator

lemma normalCoefficient_sum_eq_matrixBilinearForm
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, x i * A i j * x j) =
      TauCeti.PDE.matrixBilinearForm A x x := by
  simp only [TauCeti.PDE.matrixBilinearForm_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

lemma normalCoefficient_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (x : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, x i * orthogonalPrincipalCoefficient e a x i j * x j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (e x) i * a (e x) i j * (e x) j := by
  rw [normalCoefficient_sum_eq_matrixBilinearForm,
    normalCoefficient_sum_eq_matrixBilinearForm,
    matrixBilinearForm_eq_matrixOperator_inner, matrixBilinearForm_eq_matrixOperator_inner]
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a x) x =
      e.symm (matrixOperatorMap (a (e x)) (e x)) := by
    change (operatorMatrixMap _).toEuclideanLin x = _
    rw [operatorMatrixMap_apply]
    rfl
  rw [hMap]
  simpa only [e.symm_apply_apply] using
    e.symm.inner_map_map (matrixOperatorMap (a (e x)) (e x)) (e x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalCoefficient_sum_eq_matrixBilinearForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normalCoefficient_orthogonal_covariance
