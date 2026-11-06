import Calderon.ActualFramedJacobiVelocityRemainder
import Calderon.ActualNativeTraceGeometryRoom

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator NormalCoordinatesFrame

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData

theorem exists_actual_referenceJacobi_full_joint_jet_bound (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j : ℕ, j ≤ N →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ
        ((closedBall y0 ρ ×ˢ Icc (-ρ) ρ) ×ˢ closedBall (0 : R3) 2),
      ∀ i : Fin 3, ‖iteratedFDeriv ℝ j
        (referenceFramedJacobiVelocityRemainder g L Φ i) p‖ ≤ M := by
  have hρ : 0 < ρ := hData.1.2.1
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let K : Set ReferenceEndpointVariables := Icc (0 : ℝ) 1 ×ˢ
    ((closedBall y0 ρ ×ˢ Icc (-ρ) ρ) ×ˢ closedBall (0 : R3) 2)
  have hK : IsCompact K := isCompact_Icc.prod
    (((isCompact_closedBall y0 ρ).prod isCompact_Icc).prod (isCompact_closedBall _ _))
  apply exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (referenceFramedJacobiVelocityRemainder g L Φ) K hK _ N
  intro i p hp
  apply contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i p
  have hy : ‖p.2.1.1-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hp.2.1.1
  have hr : |p.2.1.2| ≤ ρ := abs_le.mpr hp.2.1.2
  exact referenceFramedNormalizedJacobian_isInvertible_on_actual_drift_room
    g L y0 Φ B ε C ρ H a w hData p.1 hp.1 p.2.1.1 (by linarith)
    p.2.1.2 (by linarith) p.2.2 hp.2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
