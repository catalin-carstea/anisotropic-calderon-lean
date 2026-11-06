import Calderon.ActualAngularCoordinateJets
import Calderon.ActualReferencePairedLowRadialRemainderLocalSmoothness

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
open EnergyBridge ConnectionError SphereHarmonic
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
attribute [local instance] angularHighHalfCompleteSpace angularHighNegativeCompleteSpace
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Signed actual adjoint high radial remainder `Th`. -/
def adjointHighRemainder (p : Pphys) : Hi →L[ℝ] Half :=
  secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (p.1,(p.2.1,t))) p.2.2

/-- Signed actual adjoint half radial remainder `Tl`. -/
def adjointHalfRemainder (p : Pphys) : Half →L[ℝ] NegH :=
  secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (p.1,(p.2.1,t))) p.2.2

/-- Actual sharp signed remainder `Sh(p)`. -/
def sharpRemainder (p : Pphys) : Hi →L[ℝ] Half :=
  referenceSharpRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2.1 p.2.2

/-- Actual lower sharp signed remainder `Sl(p)`. -/
def lowerSharpRemainder (p : Pphys) : Half →L[ℝ] NegH :=
  referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2.1 p.2.2

attribute [local irreducible] referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder secondTaylorRemainder
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceRadialEndpointInvertibleLocus

lemma contDiffAt_actualAngularRadialRemainder_families_of_segment
    (hreg : FixedDirichletRegularity) (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈
      referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData) p ∧
    ContDiffAt ℝ ∞ (adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData) p ∧
    ContDiffAt ℝ ∞ (sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData) p ∧
    ContDiffAt ℝ ∞ (lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData) p := by
  have hH := contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2 hSegment
  have hL := contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2 hSegment
  simpa (config := { unfoldPartialApp := true }) only [adjointHighRemainder,adjointHalfRemainder,sharpRemainder,lowerSharpRemainder]
    using And.intro hH.2 (And.intro hL.2 (And.intro hH.1 hL.1))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
