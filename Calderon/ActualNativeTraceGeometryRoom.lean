import Calderon.JointConformalReferenceFramedDriftData
import Calderon.FramedEndpointLocalChart
import Calderon.ActualCompactNormalChart

/-! Actual geometry conditions are extracted from the SAME full drift data.
No extra chart invertibility or endpoint-domain premise is assumed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open ConnectionError MetricOperator NormalCoordinatesFrame

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))).IsInvertible := by
  rcases hData.1 with ⟨hMetric,hρ,hρε,hTail⟩
  rcases hMetric with ⟨hEndpoint,hε,hC,hFrame,hBij,hSmooth,hRoom,hJets⟩
  obtain ⟨hDomain,hODE,hZero,hFirst,hQuadratic,hHalf,hLower,hUpper⟩ :=
    hRoom q hq y (hy.trans hρε) r (hr.trans hρε) z hz
  apply isInvertible_of_injective_endomorphism
  exact framedNormalizedEndpointDerivative_injective_of_lower_bound
    (fun p => (Φ q p 1).1) (metricOperatorField (conformalReferenceMatrix g L q))
    (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x)) ((y,r),z)
    (1/2) (by norm_num) hLower

theorem reference_zero_center_mem_endpointDomain_on_actual_drift_room
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) :
    (y,0) ∈ B := by
  rcases hData.1 with ⟨hMetric,hρ,hρε,hTail⟩
  rcases hMetric with ⟨hEndpoint,hε,hC,hFrame,hBij,hSmooth,hRoom,hJets⟩
  have hZeroRadius : |(0 : ℝ)| ≤ ε := by simpa only [abs_zero] using hε.le
  have hZeroSpace : (0 : R3) ∈ closedBall (0 : R3) 2 := by simp
  have hRoom0 := hRoom q hq y (hy.trans hρε) 0 hZeroRadius 0 hZeroSpace
  simpa only [zero_smul] using hRoom0.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
