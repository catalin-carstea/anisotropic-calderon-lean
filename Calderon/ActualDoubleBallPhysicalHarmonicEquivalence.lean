import Calderon.ActualDoubleBallPhysicalHarmonicCovariance

/-! Full upfront: EXPANSION-actual-double-ball-harmonic-equivalence-v001.json.
Actual nonzero Jacobian factor and bidirectional PDE equivalence, same double-ball room. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem referenceFramedNormalizedJacobian_det_ne_zero_on_doubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ ball (0 : R3) 2) :
    (operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det ≠ 0 := by
  let X : R3 → R3 := fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))
  let J : R3 →L[ℝ] R3 := referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hDX : HasFDerivAt X (r • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun x => (Φ q x 1).1)
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r
  have hAeq : coordinateJacobianMatrix X z = r • operatorMatrixMap J := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap,hDX.fderiv,map_smul]
  have hUnit : IsUnit (coordinateJacobianMatrix X z).det :=
    coordinateJacobianMatrix_referencePhysicalEndpoint_isUnit_det
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 z
        (ball_subset_closedBall hz)
  have hNe : (coordinateJacobianMatrix X z).det ≠ 0 :=
    (isUnit_iff_ne_zero).mp hUnit
  change (operatorMatrixMap J).det ≠ 0
  intro hZero
  rw [hAeq,Matrix.det_smul,Fintype.card_fin,hZero,mul_zero] at hNe
  exact hNe rfl

theorem referencePhysicalHarmonicCovariance_factor_pos_on_doubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (z : R3) (hz : z ∈ ball (0 : R3) 2) :
    0 < r^2 * |(operatorMatrixMap
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det| *
      Real.exp (-L*referenceRescaledDepth g L Φ (q,(y,r)) z) := by
  have hrSq : 0 < r^2 := by
    simpa only [pow_two] using (mul_self_pos.mpr hr0)
  have hDet : 0 < |(operatorMatrixMap
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det| :=
    abs_pos.mpr (referenceFramedNormalizedJacobian_det_ne_zero_on_doubleBall
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 z hz)
  exact mul_pos (mul_pos hrSq hDet) (Real.exp_pos _)

theorem referenceRescaledPositiveExpression_physical_pullback_zero_iff_on_doubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0) (u : SmoothData)
    (z : R3) (hz : z ∈ ball (0 : R3) 2) :
    referenceRescaledPositiveExpression g L Φ H w (q,(y,r))
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u).1 z = 0 ↔
    coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1)
      (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) = 0 := by
  have hEq := referenceRescaledPositiveExpression_physical_pullback_eq_on_doubleBall
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 u z hz
  have hPos := referencePhysicalHarmonicCovariance_factor_pos_on_doubleBall
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 z hz
  rw [hEq]
  constructor
  · intro hZero
    have hNeg := (mul_eq_zero.mp hZero).resolve_left (ne_of_gt hPos)
    exact neg_eq_zero.mp hNeg
  · intro hZero
    rw [hZero,neg_zero,mul_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFramedNormalizedJacobian_det_ne_zero_on_doubleBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalHarmonicCovariance_factor_pos_on_doubleBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRescaledPositiveExpression_physical_pullback_zero_iff_on_doubleBall
