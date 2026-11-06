import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.SignedOperatorTaylorRemainder

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-FIXED-MULTIPLIER-RADIAL-JET-EXPANSION-v001.md. Draft-only actual high fixed-Q signed remainder. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL sphereSobolevInclusionL
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily

local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderComplete1 : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderComplete2 : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderComplete3 : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance coercivityOct28ActualHighSmoothMultiplierSecondRadialRemainderComplete4 : CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

def referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r

lemma referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) :
    referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q q y 0 =
      (1/2 : ℝ) • deriv (deriv (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t)))) 0 :=
  secondTaylorRemainder_zero _

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder_zero
