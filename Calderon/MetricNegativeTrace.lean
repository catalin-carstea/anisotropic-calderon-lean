import Calderon.MetricVolumeDifferential
import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace OAI.AnisotropicCalderon.MetricVolume

lemma trace_mul_nonneg_of_posSemidef (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  let S : Mat := CFC.sqrt A
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : S * S = A := by
    simpa only [S, pow_two] using CFC.sq_sqrt A hA.nonneg
  have ht := (hB.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hsq] at ht
  exact ht

lemma trace_inverse_metric_negative_le (M H : Mat) (a : ℝ) (hM : M.PosDef)
    (hH : (-H - a • M).PosSemidef) :
    Matrix.trace (M⁻¹ * H) ≤ -3 * a := by
  have h := trace_mul_nonneg_of_posSemidef M⁻¹ (-H - a • M) hM.inv.posSemidef hH
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  rw [Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul, Matrix.nonsing_inv_mul M hunit,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_one] at h
  norm_num at h
  linarith

lemma trace_inverse_eq_coordinate_contraction (M H : Mat) (hM : M.PosDef) :
    Matrix.trace (M⁻¹ * H) = ∑ i : Fin 3, ∑ j : Fin 3, M⁻¹ i j * H i j := by
  have hs (i j : Fin 3) : M⁻¹ i j = M⁻¹ j i := by
    simpa using (hM.inv.isHermitian.apply j i)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]

lemma inverse_metric_negative_coordinate_le (M H : Mat) (a : ℝ) (hM : M.PosDef)
    (hH : (-H - a • M).PosSemidef) :
    (∑ i : Fin 3, ∑ j : Fin 3, M⁻¹ i j * H i j) ≤ -3 * a := by
  rw [← trace_inverse_eq_coordinate_contraction M H hM]
  exact trace_inverse_metric_negative_le M H a hM hH

end OAI.AnisotropicCalderon.MetricVolume
