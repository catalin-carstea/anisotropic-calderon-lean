import Calderon.MetricNegativeTrace
import Calderon.ActualPerturbedDefect

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace OAI.AnisotropicCalderon.NormalizedPrincipalMetric
open MetricVolume ConformalDepth ReferenceDensityBounds PerturbedDensityAdjoint
  ActualPerturbedDefect ActualScalarPrincipalAdjoint

/-- Strict trace positivity for the actual product of two positive definite matrices. -/
lemma trace_mul_pos_of_posDef (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    0 < Matrix.trace (A*B) := by
  let S : Mat := CFC.sqrt A
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : S*S=A := by
    simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hpow : IsUnit (S^2) := by simpa only [pow_two,hsq] using hA.isUnit
  have hunit : IsUnit S := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow
  have ht := (hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)).trace_pos
  rw [hS.isHermitian.eq,Matrix.trace_mul_cycle,hsq] at ht
  exact ht

def normalizedPrincipalMatrix (A B : Mat) : Mat :=
  (3 / Matrix.trace (A*B⁻¹)) • B⁻¹

def normalizedPrincipalDifference (A B : Mat) : Mat :=
  normalizedPrincipalMatrix A B - A⁻¹

lemma normalizedPrincipal_denominator_pos (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    0 < Matrix.trace (A*B⁻¹) := trace_mul_pos_of_posDef A B⁻¹ hA hB.inv

lemma normalizedPrincipalMatrix_isHermitian (A B : Mat) (hB : B.PosDef) :
    (normalizedPrincipalMatrix A B).IsHermitian := by
  exact hB.inv.isHermitian.smul (by simp [IsSelfAdjoint])

lemma normalizedPrincipalMatrix_posDef (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    (normalizedPrincipalMatrix A B).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (normalizedPrincipalMatrix_isHermitian A B hB) ?_
  intro v hv
  unfold normalizedPrincipalMatrix
  rw [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  exact mul_pos (div_pos (by norm_num) (normalizedPrincipal_denominator_pos A B hA hB))
    (hB.inv.dotProduct_mulVec_pos hv)

lemma normalizedPrincipalDifference_isHermitian (A B : Mat)
    (hA : A.PosDef) (hB : B.PosDef) :
    (normalizedPrincipalDifference A B).IsHermitian :=
  (normalizedPrincipalMatrix_isHermitian A B hB).sub hA.inv.isHermitian

lemma trace_mul_normalizedPrincipalMatrix (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    Matrix.trace (A*normalizedPrincipalMatrix A B) = 3 := by
  rw [normalizedPrincipalMatrix,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
  exact div_mul_cancel₀ _ (normalizedPrincipal_denominator_pos A B hA hB).ne'

lemma trace_mul_normalizedPrincipalDifference (A B : Mat) (hA : A.PosDef) (hB : B.PosDef) :
    Matrix.trace (A*normalizedPrincipalDifference A B) = 0 := by
  rw [normalizedPrincipalDifference,Matrix.mul_sub,Matrix.trace_sub,
    trace_mul_normalizedPrincipalMatrix A B hA hB,
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),Matrix.trace_one]
  norm_num

def referenceNormalizedPrincipalMatrix (g1 g2 : MatrixField) (L lam : ℝ) : MatrixField :=
  fun x => normalizedPrincipalMatrix (referenceMetric (dilatedMetric g1 lam) L x)
    (dilatedMetric g2 lam x)

def referenceNormalizedPrincipalDifference (g1 g2 : MatrixField) (L lam : ℝ) : MatrixField :=
  fun x => normalizedPrincipalDifference (referenceMetric (dilatedMetric g1 lam) L x)
    (dilatedMetric g2 lam x)

lemma referenceNormalizedPrincipalDifference_isHermitian (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L lam : ℝ) (x : R3) :
    (referenceNormalizedPrincipalDifference g1 g2 L lam x).IsHermitian := by
  exact normalizedPrincipalDifference_isHermitian _ _
    (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g1 hg1 lam) x)
    (dilatedMetric_posDef g2 hg2 lam x)

lemma referenceNormalizedPrincipalDifference_trace_eq_zero (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L lam : ℝ) (x : R3) :
    Matrix.trace (referenceMetric (dilatedMetric g1 lam) L x *
      referenceNormalizedPrincipalDifference g1 g2 L lam x) = 0 := by
  exact trace_mul_normalizedPrincipalDifference _ _
    (EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g1 hg1 lam) x)
    (dilatedMetric_posDef g2 hg2 lam x)

/-- The generic coefficient becomes the literal rQ after the source normalization. -/
lemma actualPrincipalMatrix_normalized_eq (g1 g2 : MatrixField) (L lam δ R : ℝ)
    (p : ℕ) (x : R3) :
    actualPrincipalMatrix g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) x =
      referenceRadius δ R p L x • referenceNormalizedPrincipalMatrix g1 g2 L lam x := by
  ext i j
  simp only [actualPrincipalMatrix,referenceInverseEntryFamily,referenceNormalizedPrincipalDifference,
    normalizedPrincipalDifference,referenceNormalizedPrincipalMatrix,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

lemma actualPrincipalMatrix_normalized_isHermitian (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (x : R3) :
    (actualPrincipalMatrix g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) x).IsHermitian :=
  actualPrincipalMatrix_isHermitian g1 hg1 L lam δ R p _ x
    (referenceNormalizedPrincipalDifference_isHermitian g1 g2 hg1 hg2 L lam x)

end OAI.AnisotropicCalderon.NormalizedPrincipalMetric
