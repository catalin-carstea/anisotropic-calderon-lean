import Calderon.MetricCompatibleSourceJetAlgebra

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open MetricVolume

theorem eq_smul_of_traceFreeHessianMatrix_contraction_eq_zero
    (a Z : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (hZ : ∀ i j : Fin 3, Z i j = Z j i) (h22 : a 2 2 ≠ 0)
    (hFive : ∀ k : Fin 5,
      (∑ i : Fin 3, ∑ j : Fin 3, Z i j * traceFreeHessianMatrix a k i j) = 0) :
    Z = (Z 2 2 / a 2 2) • a := by
  have h00 : Z 0 0 = (Z 2 2 / a 2 2) * a 0 0 := by
    have h := hFive 0
    norm_num [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three] at h
    field_simp [h22] at h ⊢
    nlinarith only [h]
  have h11 : Z 1 1 = (Z 2 2 / a 2 2) * a 1 1 := by
    have h := hFive 1
    norm_num [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three] at h
    field_simp [h22] at h ⊢
    nlinarith only [h]
  have h01 : Z 0 1 = (Z 2 2 / a 2 2) * a 0 1 := by
    have h := hFive 2
    norm_num [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three,
      hZ 1 0] at h
    field_simp [h22] at h ⊢
    nlinarith only [h]
  have h02 : Z 0 2 = (Z 2 2 / a 2 2) * a 0 2 := by
    have h := hFive 3
    norm_num [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three,
      hZ 2 0] at h
    field_simp [h22] at h ⊢
    nlinarith only [h]
  have h12 : Z 1 2 = (Z 2 2 / a 2 2) * a 1 2 := by
    have h := hFive 4
    norm_num [traceFreeHessianMatrix, coordinateMatrixUnit, Fin.sum_univ_three,
      hZ 2 1] at h
    field_simp [h22] at h ⊢
    nlinarith only [h]
  ext i j
  change Z i j = (Z 2 2 / a 2 2) * a i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h02
  · exact (hZ 1 0).trans (h01.trans
      (congrArg (fun z : ℝ => (Z 2 2 / a 2 2) * z) (ha 1 0).symm))
  · exact h11
  · exact h12
  · exact (hZ 2 0).trans (h02.trans
      (congrArg (fun z : ℝ => (Z 2 2 / a 2 2) * z) (ha 2 0).symm))
  · exact (hZ 2 1).trans (h12.trans
      (congrArg (fun z : ℝ => (Z 2 2 / a 2 2) * z) (ha 2 1).symm))
  · exact (div_mul_cancel₀ _ h22).symm

theorem eq_zero_of_traceFreeHessianMatrix_and_trace_contraction_eq_zero
    (a Z gamma : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (hZ : ∀ i j : Fin 3, Z i j = Z j i) (h22 : a 2 2 ≠ 0)
    (hFive : ∀ k : Fin 5,
      (∑ i : Fin 3, ∑ j : Fin 3, Z i j * traceFreeHessianMatrix a k i j) = 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0)
    (hTrace : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * Z i j) = 0) :
    Z = 0 := by
  have hForm := eq_smul_of_traceFreeHessianMatrix_contraction_eq_zero a Z ha hZ h22 hFive
  have hEntry (i j : Fin 3) : Z i j = (Z 2 2 / a 2 2) * a i j :=
    congrFun (congrFun hForm i) j
  have hProduct : (Z 2 2 / a 2 2) *
      (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) = 0 := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, gamma i j * ((Z 2 2 / a 2 2) * a i j) := by
        simp only [Finset.mul_sum, mul_left_comm (Z 2 2 / a 2 2)]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, gamma i j * Z i j := by simp_rw [← hEntry]
      _ = 0 := hTrace
  have hScalar : Z 2 2 / a 2 2 = 0 := (mul_eq_zero.mp hProduct).resolve_right hGamma
  calc
    Z = (Z 2 2 / a 2 2) • a := hForm
    _ = 0 := by rw [hScalar, zero_smul]

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra

#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.eq_smul_of_traceFreeHessianMatrix_contraction_eq_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.eq_zero_of_traceFreeHessianMatrix_and_trace_contraction_eq_zero
