import Calderon.MetricHessianTestInjectivity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra
open MetricVolume

def matrixContractionL (A : Mat) : Mat →ₗ[ℝ] ℝ where
  toFun Z := ∑ i : Fin 3, ∑ j : Fin 3, A i j * Z i j
  map_add' X Y := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum, mul_left_comm c]

def hessianTestL (a gamma : Mat) : Mat →ₗ[ℝ] Mat := by
  let F : Mat → Mat := fun Z =>
    ![![matrixContractionL (traceFreeHessianMatrix a 0) Z,
        matrixContractionL (traceFreeHessianMatrix a 1) Z,
        matrixContractionL (traceFreeHessianMatrix a 2) Z],
      ![matrixContractionL (traceFreeHessianMatrix a 3) Z,
        matrixContractionL (traceFreeHessianMatrix a 4) Z,
        matrixContractionL gamma Z],
      ![Z 0 1 - Z 1 0, Z 0 2 - Z 2 0, Z 1 2 - Z 2 1]]
  refine { toFun := F, map_add' := ?_, map_smul' := ?_ }
  · intro X Y
    ext i j
    change F (X + Y) i j = F X i j + F Y i j
    fin_cases i <;> fin_cases j <;> simp [F, map_add, Matrix.add_apply] <;> ring
  · intro c Z
    ext i j
    change F (c • Z) i j = c * F Z i j
    fin_cases i <;> fin_cases j <;>
      simp [F, map_smul, Matrix.smul_apply, smul_eq_mul] <;> ring

lemma eq_zero_of_hessianTestL_eq_zero
    (a gamma Z : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (h22 : a 2 2 ≠ 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0)
    (h : hessianTestL a gamma Z = 0) : Z = 0 := by
  have h00 : matrixContractionL (traceFreeHessianMatrix a 0) Z = 0 :=
    congrFun (congrFun h 0) 0
  have h01 : matrixContractionL (traceFreeHessianMatrix a 1) Z = 0 :=
    congrFun (congrFun h 0) 1
  have h02 : matrixContractionL (traceFreeHessianMatrix a 2) Z = 0 :=
    congrFun (congrFun h 0) 2
  have h10 : matrixContractionL (traceFreeHessianMatrix a 3) Z = 0 :=
    congrFun (congrFun h 1) 0
  have h11 : matrixContractionL (traceFreeHessianMatrix a 4) Z = 0 :=
    congrFun (congrFun h 1) 1
  have h12 : matrixContractionL gamma Z = 0 := congrFun (congrFun h 1) 2
  have h20 : Z 0 1 - Z 1 0 = 0 := congrFun (congrFun h 2) 0
  have h21 : Z 0 2 - Z 2 0 = 0 := congrFun (congrFun h 2) 1
  have h22' : Z 1 2 - Z 2 1 = 0 := congrFun (congrFun h 2) 2
  have hZ : ∀ i j : Fin 3, Z i j = Z j i := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact sub_eq_zero.mp h20
    · exact sub_eq_zero.mp h21
    · exact (sub_eq_zero.mp h20).symm
    · rfl
    · exact sub_eq_zero.mp h22'
    · exact (sub_eq_zero.mp h21).symm
    · exact (sub_eq_zero.mp h22').symm
    · rfl
  have hFive : ∀ k : Fin 5,
      (∑ i : Fin 3, ∑ j : Fin 3, Z i j * traceFreeHessianMatrix a k i j) = 0 := by
    intro k
    fin_cases k
    · simpa [matrixContractionL, traceFreeHessianMatrix, mul_comm] using h00
    · simpa [matrixContractionL, traceFreeHessianMatrix, mul_comm] using h01
    · simpa [matrixContractionL, traceFreeHessianMatrix, mul_comm] using h02
    · simpa [matrixContractionL, traceFreeHessianMatrix, mul_comm] using h10
    · simpa [matrixContractionL, traceFreeHessianMatrix, mul_comm] using h11
  exact eq_zero_of_traceFreeHessianMatrix_and_trace_contraction_eq_zero
    a Z gamma ha hZ h22 hFive hGamma h12

lemma hessianTestL_injective
    (a gamma : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (h22 : a 2 2 ≠ 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0) :
    Function.Injective (hessianTestL a gamma) := by
  intro X Y hXY
  apply sub_eq_zero.mp
  apply eq_zero_of_hessianTestL_eq_zero a gamma (X-Y) ha h22 hGamma
  rw [map_sub, hXY, sub_self]

def hessianTestEquiv
    (a gamma : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (h22 : a 2 2 ≠ 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0) :
    Mat ≃ₗ[ℝ] Mat :=
  LinearEquiv.ofInjectiveEndo (hessianTestL a gamma)
    (hessianTestL_injective a gamma ha h22 hGamma)

lemma hessianTestEquiv_apply
    (a gamma : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (h22 : a 2 2 ≠ 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0) (Z : Mat) :
    hessianTestEquiv a gamma ha h22 hGamma Z = hessianTestL a gamma Z := rfl

lemma hessianTestEquiv_symm_apply_test
    (a gamma : Mat) (ha : ∀ i j : Fin 3, a i j = a j i)
    (h22 : a 2 2 ≠ 0)
    (hGamma : (∑ i : Fin 3, ∑ j : Fin 3, gamma i j * a i j) ≠ 0) (Z : Mat) :
    (hessianTestEquiv a gamma ha h22 hGamma).symm (hessianTestL a gamma Z) = Z :=
  (hessianTestEquiv a gamma ha h22 hGamma).symm_apply_apply Z

end OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra

#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.matrixContractionL
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.hessianTestL
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.eq_zero_of_hessianTestL_eq_zero
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.hessianTestL_injective
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.hessianTestEquiv
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.hessianTestEquiv_apply
#print axioms OAI.AnisotropicCalderon.ExteriorSource.MetricCompatibleSourceJetAlgebra.hessianTestEquiv_symm_apply_test
