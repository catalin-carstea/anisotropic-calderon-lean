import Calderon.CompactParameterReferenceDrift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open ConnectionError NormalCoordinatesFrame MetricOperator EnergyBridge

def jointReferenceRadialReorder {V : Type}
    (f : (ℝ × (R3 × ℝ)) × R3 → V) (p : ((ℝ × R3) × ℝ) × R3) : V :=
  f ((p.1.1.1,(p.1.1.2,p.1.2)),p.2)

theorem contDiff_jointReferenceRadialReorder {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × (R3 × ℝ)) × R3 → V) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (jointReferenceRadialReorder f) := by
  exact hf.comp
    ((contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk contDiff_snd)

def JointConformalReferenceFramedDriftData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) : Prop :=
  ConformalReferencePositiveCoefficientData g L y0 Φ B ε C ρ H a w ∧
  ContDiff ℝ ∞ (conformalReferenceFramedDriftBase g L Φ H) ∧
  ContDiff ℝ ∞ (conformalReferenceFramedDrift g L Φ H) ∧
  ContDiff ℝ ∞ (conformalReferenceWeightedFramedDrift g L Φ H w) ∧
  (∀ p, a p = w p • (H p)⁻¹) ∧
  (∀ p, conformalReferenceWeightedFramedDrift g L Φ H w p =
    w p • conformalReferenceFramedDrift g L Φ H p) ∧
  (∀ p, 3 ≤ ‖p.2‖ → conformalReferenceWeightedFramedDrift g L Φ H w p = 0) ∧
  (∀ q : ℝ, ∀ y z : R3,
    conformalReferenceFramedDrift g L Φ H ((q,(y,0)),z) = 0 ∧
    conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,0)),z) = 0) ∧
  (∀ q : ℝ, ∀ y z : R3,
    HasDerivAt (fun r : ℝ => conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z))
      (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0 ∧
    HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (-L • (w ((q,(y,0)),z) • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z))) 0) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
    HasDerivAt (fun r : ℝ => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z))
      (-L • conformalReferenceFramedDriftBase g L Φ H ((q,(y,0)),z)) 0) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ →
    ∀ z ∈ closedBall (0 : R3) 2,
      referenceFramedNormalOperatorForCoefficients g L Φ ((q,(y,r)),z)
        (conformalReferenceFramedDrift g L Φ H ((q,(y,r)),z)) =
      (-L*r) • ((parameterFramedNormalizedEndpointDerivative (fun p => (Φ p.1 p.2 1).1)
        (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z)).adjoint
          (gradient conformalReferenceCoordinateDepth
            (parameterFramedScaledEndpoint (fun p => (Φ p.1 p.2 1).1)
              (conformalReferenceGramFrameOperatorJoint g L) ((q,(y,r)),z))))) ∧
  CompactMixedLinearBounds
    (referenceCoefficientRadialReorder (conformalReferenceFramedDrift g L Φ H))
    (referenceCoefficientNonradialRoom y0 ρ) ρ ∧
  CompactMixedLinearBounds
    (referenceCoefficientRadialReorder (conformalReferenceWeightedFramedDrift g L Φ H w))
    (referenceCoefficientNonradialRoom y0 ρ) ρ ∧
  ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧
    (∀ j : ℕ, j ≤ N → ∀ p ∈ referenceDriftCompactRoom y0 ρ,
      ‖iteratedFDeriv ℝ j (conformalReferenceFramedDriftBase g L Φ H) p‖ ≤ D ∧
      ‖iteratedFDeriv ℝ j (conformalReferenceFramedDrift g L Φ H) p‖ ≤ D ∧
      ‖iteratedFDeriv ℝ j (conformalReferenceWeightedFramedDrift g L Φ H w) p‖ ≤ D) ∧
    ∀ p ∈ referenceDriftCompactRoom y0 ρ,
      ‖conformalReferenceFramedDrift g L Φ H p‖ ≤ D*|p.1.2.2| ∧
      ‖conformalReferenceWeightedFramedDrift g L Φ H w p‖ ≤ D*|p.1.2.2|

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
