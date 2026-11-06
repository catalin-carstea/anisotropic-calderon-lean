import Calderon.ActualPhysicalPullbackMetric
import Calderon.MetricPullbackFlux
/-! C4 normalization stage: exact matrix normalization and derivative
invertibility, with no chart/invertibility/covariance premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily.DriftBootstrap

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem pullbackMetric_referenceOriginal_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z =
      (r^2 * Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z)) • H ((q,(y,r)),z) := by
  ext i j
  have hMetric := referencePhysicalPullbackMetric_inner g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr z hz (coordinateVector j) (coordinateVector i)
  rw [matrixOperator_basis_inner] at hMetric
  have hEntry := matrixOperator_basis_inner
    (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z) i j
  change inner ℝ ((pullbackMetric (fun x => g (q • x))
    (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z).toEuclideanLin
      (coordinateVector j)) (coordinateVector i) = _ at hEntry
  unfold pullbackMetric at hEntry
  rw [operatorMatrixMap_apply] at hEntry
  simp only [ContinuousLinearMap.comp_apply] at hEntry
  rw [ContinuousLinearMap.adjoint_inner_left] at hEntry
  change (pullbackMetric (fun x => g (q • x))
    (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z) i j =
      (r^2 * Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z)) * H ((q,(y,r)),z) i j
  exact hEntry.symm.trans hMetric

theorem pullbackMetric_referenceOriginal_eq_conformal
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z =
      conformalMatrix (fun x => H ((q,(y,r)),x))
        (fun x => Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) x) z := by
  have hExp : Real.exp (2*Real.log |r|) = r^2 := by
    rw [two_mul,Real.exp_add]
    simp only [Real.exp_log (abs_pos.mpr hr0),← pow_two,sq_abs]
  rw [pullbackMetric_referenceOriginal_eq g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr z hz]
  change (r^2 * Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z)) • H ((q,(y,r)),z) =
    Real.exp (2*(Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) z)) • H ((q,(y,r)),z)
  have hPower : 2*(Real.log |r| + L*referenceRescaledDepth g L Φ (q,(y,r)) z) =
      2*Real.log |r| + 2*L*referenceRescaledDepth g L Φ (q,(y,r)) z := by ring
  rw [hPower,Real.exp_add,hExp]

theorem coordinateJacobianMatrix_referencePhysicalEndpoint_isUnit_det
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    IsUnit (coordinateJacobianMatrix
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z).det := by
  let X := fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))
  let A := coordinateJacobianMatrix X z
  have hPositive := hData.1
  rcases hPositive with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  have hPbPos : (pullbackMetric (fun x => g (q • x)) X z).PosDef := by
    rw [pullbackMetric_referenceOriginal_eq_conformal g hg L y0 Φ B ε C ρ H a w hData
      q hq y hy r hr hr0 z hz]
    exact conformalMatrix_posDef _ _ (fun x => hPos ((q,(y,r)),x)) z
  have hMat : pullbackMetric (fun x => g (q • x)) X z = A.transpose * g (q • X z) * A := by
    simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
      operatorMatrixMap_metricOperatorField,A,coordinateJacobianMatrix_eq_operatorMatrixMap,Matrix.mul_assoc]
  change IsUnit A.det
  apply (isUnit_iff_ne_zero).mpr
  intro hZero
  have hDet := hPbPos.det_pos
  rw [hMat,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hZero,mul_zero] at hDet
  exact (lt_irrefl (0 : ℝ)) hDet

end OAI.AnisotropicCalderon.ConnectionError
