import Calderon.ActualCompactNormalChart
import Calderon.ActualRescaledConformalGauge
/-! Source-only author stage C1. Exact input copies, full covariance expansion,
and literal C1 interfaces were sealed before these proof bodies. C2-C5 remain
implementation obligations; no physical/native kernel or Psi theorem claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily.DriftBootstrap

def referenceFramedOriginalNormalizedMetric (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (p : (ℝ × (R3 × ℝ)) × R3) : R3 →L[ℝ] R3 :=
  let J := referenceFramedNormalizedJacobian g L Φ (p.1.1,(p.1.2,p.2))
  let X := referenceFramedPhysicalEndpoint g L Φ (p.1.1,(p.1.2,p.2))
  J.adjoint.comp ((metricOperatorField g (p.1.1 • X)).comp J)

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData

theorem referenceFramedOriginalNormalizedMetric_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    referenceFramedOriginalNormalizedMetric g L Φ ((q,(y,r)),z) =
      Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z) •
        matrixOperatorMap (H ((q,(y,r)),z)) := by
  rcases hData.1 with ⟨_,_,_,_,_,_,_,_,_,_,_,hLocal,_,_,_⟩
  have hLocalz := hLocal q hq y hy r hr z hz
  let J := referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))
  let X := referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))
  let t := referenceRescaledDepth g L Φ (q,(y,r)) z
  have hHG : matrixOperatorMap (H ((q,(y,r)),z)) =
      referenceFramedNormalOperatorForCoefficients g L Φ ((q,(y,r)),z) := by
    rw [hLocalz.1]
    apply ContinuousLinearMap.ext
    intro V
    exact operatorMatrixMap_apply _ V
  have hInner (V W : R3) :
      inner ℝ (matrixOperatorMap (H ((q,(y,r)),z)) V) W =
        Real.exp (-2*L*t) *
          inner ℝ (referenceFramedOriginalNormalizedMetric g L Φ ((q,(y,r)),z) V) W := by
    rw [hHG]
    change inner ℝ (framedNormalizedEndpointMetric (fun x => (Φ q x 1).1)
      (metricOperatorField (conformalReferenceMatrix g L q))
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)) ((y,r),z) V) W = _
    rw [framedNormalizedEndpointMetric_inner]
    change inner ℝ (conformalReferenceOperatorJoint g L (q,X) (J V)) (J W) =
      Real.exp (-2*L*t) * inner ℝ (J.adjoint (metricOperatorField g (q • X) (J V))) W
    rw [ContinuousLinearMap.adjoint_inner_left,conformalReferenceOperatorJoint_eq]
    simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left]
    rfl
  have hExp : Real.exp (2*L*t) * Real.exp (-2*L*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  apply ContinuousLinearMap.ext
  intro V
  apply ext_inner_right ℝ
  intro W
  simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left]
  rw [hInner,← mul_assoc,hExp,one_mul]

theorem referencePhysicalPullbackMetric_inner
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (V W : R3) :
    inner ℝ (metricOperatorField g
      (q • referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
      (fderiv ℝ (fun x : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z V))
      (fderiv ℝ (fun x : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))) z W) =
      (r^2 * Real.exp (2*L*referenceRescaledDepth g L Φ (q,(y,r)) z)) *
        inner ℝ (matrixOperatorMap (H ((q,(y,r)),z)) V) W := by
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : HasFDerivAt
      (fun x : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))
      (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun x => (Φ q x 1).1)
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (hΘ.comp (contDiff_const.prodMk contDiff_id)) y z r
  rw [hX.fderiv]
  simp only [ContinuousLinearMap.smul_apply,map_smul,real_inner_smul_left,real_inner_smul_right]
  have hMetric := congrArg
    (fun M : R3 →L[ℝ] R3 => inner ℝ (M V) W)
    (referenceFramedOriginalNormalizedMetric_eq g hg L y0 Φ B ε C ρ H a w hData
      q hq y hy r hr z hz)
  change inner ℝ ((referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))).adjoint
      (metricOperatorField g (q • referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
        (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) V))) W = _ at hMetric
  rw [ContinuousLinearMap.adjoint_inner_left] at hMetric
  simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left] at hMetric
  rw [hMetric]
  ring

end OAI.AnisotropicCalderon.ConnectionError
