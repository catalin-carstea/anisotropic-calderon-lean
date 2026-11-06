import Calderon.NativeSupportedAdjointH2Regularity
import Calderon.NativeOrthogonalCoefficientEnergyCovariance
import Calderon.CoordinatePiolaCovariance
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume

lemma nativeSupportedDriftDivergence_eq_matrix_trace
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (x : R3) :
    nativeSupportedDriftDivergence beta x = (operatorMatrixMap (fderiv ℝ beta x)).trace := by
  unfold nativeSupportedDriftDivergence Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i hi
  have hProj : HasFDerivAt (fun y : R3 => beta y i)
      ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).comp (fderiv ℝ beta x)) x :=
    (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hbeta.differentiable (by simp) x).hasFDerivAt)
  have hDerivative := congrArg (fun A : R3 →L[ℝ] ℝ => A (coordinateVector i)) hProj.fderiv
  have hEntry := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i i)
    (coordinateJacobianMatrix_eq_operatorMatrixMap beta x)
  exact hDerivative.trans hEntry

lemma trace_operatorMatrixMap_orthogonal_conjugation
    (e : R3 ≃ₗᵢ[ℝ] R3) (T : R3 →L[ℝ] R3) :
    (operatorMatrixMap (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp e.toContinuousLinearEquiv.toContinuousLinearMap))).trace =
      (operatorMatrixMap T).trace := by
  let E := e.toContinuousLinearEquiv.toContinuousLinearMap
  let F := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hEF : E.comp F = ContinuousLinearMap.id ℝ R3 := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = 1 := by
    change matrixOperatorAlgEquiv.symm (1 : R3 →L[ℝ] R3) = 1
    exact matrixOperatorAlgEquiv.symm.map_one
  let A : Matrix (Fin 3) (Fin 3) ℝ := operatorMatrixMap F
  let B : Matrix (Fin 3) (Fin 3) ℝ := operatorMatrixMap T
  let C : Matrix (Fin 3) (Fin 3) ℝ := operatorMatrixMap E
  have hCA : C*A=1 := (operatorMatrixMap_comp E F).symm.trans
    ((congrArg operatorMatrixMap hEF).trans hId)
  have hTrace : (A*(B*C)).trace=B.trace :=
    (congrArg Matrix.trace (Matrix.mul_assoc A B C).symm).trans
      ((Matrix.trace_mul_cycle A B C).trans
        ((congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => (M*B).trace) hCA).trans
          (congrArg Matrix.trace (Matrix.one_mul B))))
  have hMat := (operatorMatrixMap_comp F (T.comp E)).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => A*M) (operatorMatrixMap_comp T E))
  exact (congrArg Matrix.trace hMat).trans hTrace

lemma fderiv_orthogonalDriftCoefficient
    (e : R3 ≃ₗᵢ[ℝ] R3) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (x : R3) :
    fderiv ℝ (orthogonalDriftCoefficient e beta) x =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ beta (e x)).comp e.toContinuousLinearEquiv.toContinuousLinearMap) := by
  let E := e.toContinuousLinearEquiv.toContinuousLinearMap
  let F := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hInner : HasFDerivAt (fun y : R3 => beta (e y))
      ((fderiv ℝ beta (e x)).comp E) x :=
    (hbeta.differentiable (by simp) (e x)).hasFDerivAt.comp x E.hasFDerivAt
  have hOuter : HasFDerivAt (orthogonalDriftCoefficient e beta)
      (F.comp ((fderiv ℝ beta (e x)).comp E)) x := F.hasFDerivAt.comp x hInner
  exact hOuter.fderiv

lemma nativeSupportedDriftDivergence_orthogonalDriftCoefficient
    (e : R3 ≃ₗᵢ[ℝ] R3) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (x : R3) :
    nativeSupportedDriftDivergence (orthogonalDriftCoefficient e beta) x =
      nativeSupportedDriftDivergence beta (e x) := by
  have hRot : ContDiff ℝ ∞ (orthogonalDriftCoefficient e beta) :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
      (hbeta.comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff)
  exact (nativeSupportedDriftDivergence_eq_matrix_trace _ hRot x).trans
    ((congrArg (fun A : R3 →L[ℝ] R3 => (operatorMatrixMap A).trace)
      (fderiv_orthogonalDriftCoefficient e beta hbeta x)).trans
      ((trace_operatorMatrixMap_orthogonal_conjugation e (fderiv ℝ beta (e x))).trans
        (nativeSupportedDriftDivergence_eq_matrix_trace beta hbeta (e x)).symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedDriftDivergence_eq_matrix_trace
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.trace_operatorMatrixMap_orthogonal_conjugation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_orthogonalDriftCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedDriftDivergence_orthogonalDriftCoefficient
