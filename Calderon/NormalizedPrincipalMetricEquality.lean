import Calderon.NormalizedPrincipalMetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.NormalizedPrincipalMetric
open MetricVolume

lemma eq_smul_of_normalizedPrincipalDifference_eq_zero
    (A B : Mat) (hA : A.PosDef) (hB : B.PosDef)
    (h : normalizedPrincipalDifference A B = 0) :
    B = (3 / Matrix.trace (A*B⁻¹)) • A := by
  have hInv : (3 / Matrix.trace (A*B⁻¹)) • B⁻¹ = A⁻¹ :=
    sub_eq_zero.mp h
  have hAInv : A*A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hBInv : B⁻¹*B = 1 :=
    Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  calc
    B = A*(A⁻¹*B) := by rw [← Matrix.mul_assoc,hAInv,Matrix.one_mul]
    _ = (3 / Matrix.trace (A*B⁻¹)) • A := by
      rw [← hInv,Matrix.smul_mul,hBInv,Matrix.mul_smul,Matrix.mul_one]

end OAI.AnisotropicCalderon.NormalizedPrincipalMetric
#print axioms OAI.AnisotropicCalderon.NormalizedPrincipalMetric.eq_smul_of_normalizedPrincipalDifference_eq_zero
