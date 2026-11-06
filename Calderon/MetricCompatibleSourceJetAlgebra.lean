import Calderon.NativeMetricJetIdentity
import Calderon.MetricCoefficient

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open EnergyBridge MetricVolume Literature

def coordinateMatrixUnit (i j : Fin 3) : Mat :=
  fun k l => if k = i ∧ l = j then 1 else 0

def matrixJetBilinear (M : Mat) : R3 →L[ℝ] (R3 →L[ℝ] ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    M i j • (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)

lemma matrixJetBilinear_apply (M : Mat) (v w : R3) :
    matrixJetBilinear M v w = ∑ i : Fin 3, ∑ j : Fin 3, M i j * (v i * w j) := by
  simp [matrixJetBilinear, Fin.sum_univ_three, mul_assoc]

lemma matrixJetBilinear_coordinateVector (M : Mat) (i j : Fin 3) :
    matrixJetBilinear M (coordinateVector i) (coordinateVector j) = M i j := by
  rw [matrixJetBilinear_apply]
  simp [coordinateVector, PiLp.single_apply]

lemma matrixJetBilinear_symmetric (M : Mat)
    (hM : ∀ i j : Fin 3, M i j = M j i) (v w : R3) :
    matrixJetBilinear M v w = matrixJetBilinear M w v := by
  rw [matrixJetBilinear_apply, matrixJetBilinear_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

def traceFreeHessianMatrix (a : Mat) : Fin 5 → Mat :=
  ![coordinateMatrixUnit 0 0 - (a 0 0 / a 2 2) • coordinateMatrixUnit 2 2,
    coordinateMatrixUnit 1 1 - (a 1 1 / a 2 2) • coordinateMatrixUnit 2 2,
    coordinateMatrixUnit 0 1 + coordinateMatrixUnit 1 0 -
      (2 * a 0 1 / a 2 2) • coordinateMatrixUnit 2 2,
    coordinateMatrixUnit 0 2 + coordinateMatrixUnit 2 0 -
      (2 * a 0 2 / a 2 2) • coordinateMatrixUnit 2 2,
    coordinateMatrixUnit 1 2 + coordinateMatrixUnit 2 1 -
      (2 * a 1 2 / a 2 2) • coordinateMatrixUnit 2 2]

lemma traceFreeHessianMatrix_symmetric (a : Mat) (k : Fin 5) (i j : Fin 3) :
    traceFreeHessianMatrix a k i j = traceFreeHessianMatrix a k j i := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [traceFreeHessianMatrix, coordinateMatrixUnit]

lemma traceFreeHessianMatrix_contraction_eq_zero (a : Mat)
    (hSym : ∀ i j : Fin 3, a i j = a j i) (h22 : a 2 2 ≠ 0) (k : Fin 5) :
    (∑ i : Fin 3, ∑ j : Fin 3, a i j * traceFreeHessianMatrix a k i j) = 0 := by
  have h10 : a 1 0 = a 0 1 := hSym 1 0
  have h20 : a 2 0 = a 0 2 := hSym 2 0
  have h21 : a 2 1 = a 1 2 := hSym 2 1
  fin_cases k <;>
    simp [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three,
      h10, h20, h21] <;> field_simp [h22] <;> ring

lemma nativeMetricJetFunctional_traceFreeHessianMatrix
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (k : Fin 5) :
    nativeMetricJetFunctional g p 0
      (matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k)) = 0 := by
  apply (nativeMetricJetFunctional_eq_zero_iff_covariantTrace_eq_zero g hg p 0 _).2
  simp only [ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero,
    sub_zero, matrixJetBilinear_coordinateVector]
  apply traceFreeHessianMatrix_contraction_eq_zero
  · intro i j
    simpa using ((hg.posDef p).inv.isHermitian.apply j i)
  · exact ne_of_gt ((hg.posDef p).inv.diag_pos (i := (2 : Fin 3)))

def coordinateJetDrift (g : MatrixField) (p : R3) (ξ : R3 →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    fderiv ℝ (fun z => principalCoefficient g z i j) p (coordinateVector i) *
      ξ (coordinateVector j)

def gradientCorrectionHessianMatrix (g : MatrixField) (p : R3)
    (ξ : R3 →L[ℝ] ℝ) : Mat :=
  (-(coordinateJetDrift g p ξ) / principalCoefficient g p 2 2) •
    coordinateMatrixUnit 2 2

lemma gradientCorrectionHessianMatrix_symmetric
    (g : MatrixField) (p : R3) (ξ : R3 →L[ℝ] ℝ) (i j : Fin 3) :
    gradientCorrectionHessianMatrix g p ξ i j =
      gradientCorrectionHessianMatrix g p ξ j i := by
  fin_cases i <;> fin_cases j <;>
    simp [gradientCorrectionHessianMatrix, coordinateMatrixUnit]

lemma nativeMetricJetFunctional_matrixJetBilinear
    (g : MatrixField) (p : R3) (ξ : R3 →L[ℝ] ℝ) (M : Mat) :
    nativeMetricJetFunctional g p ξ (matrixJetBilinear M) =
      -(coordinateJetDrift g p ξ +
        ∑ i : Fin 3, ∑ j : Fin 3, principalCoefficient g p i j * M i j) := by
  simp only [nativeMetricJetFunctional, matrixJetBilinear_coordinateVector,
    Finset.sum_add_distrib, coordinateJetDrift]

lemma nativeMetricJetFunctional_gradientCorrectionHessianMatrix
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3) (ξ : R3 →L[ℝ] ℝ) :
    nativeMetricJetFunctional g p ξ
      (matrixJetBilinear (gradientCorrectionHessianMatrix g p ξ)) = 0 := by
  have h22 : principalCoefficient g p 2 2 ≠ 0 :=
    ne_of_gt ((principalCoefficient_posDef g hg p).diag_pos (i := (2 : Fin 3)))
  rw [nativeMetricJetFunctional_matrixJetBilinear]
  simp only [gradientCorrectionHessianMatrix, Fin.sum_univ_three,
    Matrix.smul_apply, smul_eq_mul, coordinateMatrixUnit]
  norm_num <;> field_simp [h22] <;> ring

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.matrixJetBilinear_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.matrixJetBilinear_coordinateVector
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.matrixJetBilinear_symmetric
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.traceFreeHessianMatrix_symmetric
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.traceFreeHessianMatrix_contraction_eq_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.nativeMetricJetFunctional_traceFreeHessianMatrix
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.gradientCorrectionHessianMatrix_symmetric
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.nativeMetricJetFunctional_matrixJetBilinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.nativeMetricJetFunctional_gradientCorrectionHessianMatrix
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.coordinateMatrixUnit
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.matrixJetBilinear
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.traceFreeHessianMatrix
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.coordinateJetDrift
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.gradientCorrectionHessianMatrix
