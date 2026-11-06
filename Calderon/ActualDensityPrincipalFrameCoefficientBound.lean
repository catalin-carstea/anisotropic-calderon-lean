import Calderon.ActualNormalizedScalarFrameOperator
import Calderon.MetricKoszulCoordinates

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace Matrix
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NormalizedPrincipalMetric ActualHorizontalNormBridge ReferenceDensityBounds
  SmoothMetricFrame ConformalDepth MetricOperator MetricVolume RadiusProfile

lemma referenceDensityPrincipalFrameCoefficient_posSemidef
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) :
    Matrix.PosSemidef (Matrix.of (fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j)) := by
  let A := referenceMetric (dilatedMetric g q) L y
  let N := referenceNormalizedPrincipalMatrix g g2 L q y
  let C : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun k i => referenceCoFrameEntry g L k i (q,y))
  have hN : N.PosDef := normalizedPrincipalMatrix_posDef _ _
    (dilatedReferenceMetric_posDef g hg q L y) (dilatedMetric_posDef g2 hg2 q y)
  have hPSD := hN.posSemidef.conjTranspose_mul_mul_same C
  convert hPSD using 1
  ext i j
  simp only [Matrix.of_apply, referenceDensityPrincipalFrameCoefficient, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial, Fin.sum_univ_three, C, N]
  ring

lemma trace_referenceDensityPrincipalFrameCoefficient
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) :
    Matrix.trace (fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) = 3 := by
  let A := referenceMetric (dilatedMetric g q) L y
  let N := referenceNormalizedPrincipalMatrix g g2 L q y
  let B0 : R3 →L[ℝ] R3 →L[ℝ] ℝ := (innerSL ℝ).comp (matrixOperatorMap A)
  have hBasis (k l : Fin 3) : B0 (coordinateDirection k) (coordinateDirection l) = A l k := by
    change ⟪matrixOperatorMap A (MetricVolume.coordinateVector k), MetricVolume.coordinateVector l⟫_ℝ = A l k
    exact matrixOperator_basis_inner A l k
  have hFrame (i j : Fin 3) :
      B0 (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j) =
        if i=j then 1 else 0 :=
    referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (q,y) i j
  have hContract := referenceDensityPrincipalFrameCoefficient_bilinear_contraction g hg g2 L q y B0
  have hLeft : (∑ k : Fin 3, ∑ l : Fin 3, N k l * B0 (coordinateDirection k) (coordinateDirection l)) =
      Matrix.trace (A*N) := by
    simp only [hBasis, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hRight : (∑ i : Fin 3, ∑ j : Fin 3,
      referenceDensityPrincipalFrameCoefficient g g2 L q y i j *
        B0 (referenceMetricGramFrame g L (q,y) i) (referenceMetricGramFrame g L (q,y) j)) =
      Matrix.trace (fun i j : Fin 3 => referenceDensityPrincipalFrameCoefficient g g2 L q y i j) := by
    simp [hFrame, Matrix.trace, Matrix.diag]
  have hTrace : Matrix.trace (A*N) = 3 := trace_mul_normalizedPrincipalMatrix _ _
    (dilatedReferenceMetric_posDef g hg q L y) (dilatedMetric_posDef g2 hg2 q y)
  exact hRight.symm.trans (hContract.symm.trans (hLeft.trans hTrace))

lemma abs_referenceDensityPrincipalFrameCoefficient_le_three
    (g g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
    (L q : ℝ) (y : R3) (i j : Fin 3) :
    |referenceDensityPrincipalFrameCoefficient g g2 L q y i j| ≤ 3 := by
  let Q : Matrix (Fin 3) (Fin 3) ℝ := fun i j => referenceDensityPrincipalFrameCoefficient g g2 L q y i j
  have hQ : Q.PosSemidef := referenceDensityPrincipalFrameCoefficient_posSemidef g g2 hg hg2 L q y
  have hTrace : Matrix.trace Q = 3 := trace_referenceDensityPrincipalFrameCoefficient g g2 hg hg2 L q y
  have hDiag (k : Fin 3) : 0 ≤ Q k k := hQ.diag_nonneg
  have hDiagBound (k : Fin 3) : Q k k ≤ 3 := by
    have hLe : Q k k ≤ ∑ l : Fin 3, Q l l :=
      Finset.single_le_sum (fun l _ => hDiag l) (Finset.mem_univ k)
    exact hLe.trans_eq hTrace
  change |Q i j| ≤ 3
  by_cases hij : i=j
  · subst j
    rw [abs_of_nonneg (hDiag i)]
    exact hDiagBound i
  · have hSym : Q j i = Q i j := by
      have h := congrFun (congrFun hQ.isHermitian.eq i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using h
    have hPlus := hQ.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    have hMinus := hQ.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    have hPlus' : 0 ≤ Q i i + 2*Q i j + Q j j := by
      simpa [dotProduct, Matrix.mulVec, Pi.single_apply, hij, Ne.symm hij, hSym,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, add_mul, mul_sub, sub_mul,
        two_mul, add_assoc, add_left_comm, add_comm] using hPlus
    have hMinus' : 0 ≤ Q i i - 2*Q i j + Q j j := by
      simpa [dotProduct, Matrix.mulVec, Pi.single_apply, hij, Ne.symm hij, hSym,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, add_mul, mul_sub, sub_mul,
        two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hMinus
    rw [abs_le]
    constructor <;> linarith [hDiagBound i, hDiagBound j]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceDensityPrincipalFrameCoefficient_posSemidef
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.trace_referenceDensityPrincipalFrameCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.abs_referenceDensityPrincipalFrameCoefficient_le_three
