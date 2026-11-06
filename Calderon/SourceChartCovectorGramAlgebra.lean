import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace OAI.AnisotropicCalderon.ConnectionError

lemma covectorGram_eq_of_pullback
    (K1 K2 G1 G2 J : Matrix (Fin 3) (Fin 3) ℝ)
    (hMetric : G2 = Jᵀ * G1 * J) (hCoordinates : K2 = K1 * J)
    (hJ : IsUnit J.det) :
    K2 * G2⁻¹ * K2ᵀ = K1 * G1⁻¹ * K1ᵀ := by
  have hJT : IsUnit Jᵀ.det := by
    simpa only [Matrix.det_transpose] using hJ
  rw [hCoordinates, hMetric, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left (A := J) _ hJ,
    Matrix.nonsing_inv_mul_cancel_left (A := Jᵀ) _ hJT]

lemma det_ne_zero_of_covectorGram_eq
    (A B G H : Matrix (Fin 3) (Fin 3) ℝ)
    (hGram : A * G * Aᵀ = B * H * Bᵀ)
    (hB : B.det ≠ 0) (hH : H.det ≠ 0) : A.det ≠ 0 := by
  have hdet := congrArg Matrix.det hGram
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  intro hA
  have hzero : B.det * H.det * B.det = 0 := by
    simpa only [hA, zero_mul, mul_zero] using hdet.symm
  exact (mul_ne_zero (mul_ne_zero hB hH) hB) hzero

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.covectorGram_eq_of_pullback
#print axioms OAI.AnisotropicCalderon.ConnectionError.det_ne_zero_of_covectorGram_eq
