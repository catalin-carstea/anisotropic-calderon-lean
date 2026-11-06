import Calderon.ActualFiniteHarmonicProductHighRadialGraph
import Calderon.SignedTaylorFixedLinearTransport

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
FINITE-PRODUCT-NORMALIZED-RADIAL-DOMAIN-EXPANSION-v001.md. Actual higher signed remainder with Q frozen. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3ThreeHalfRadialTrace NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHarmonicLiftFamily referenceStrongDriftFamily
  nativeThreeHalfOutwardTraceL nativeFiniteHarmonicProductLiftL

lemma contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_fixed
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q) p := by
  unfold referenceFiniteHarmonicProductHighRadialFamily
  exact contDiffAt_const.clm_comp
    ((contDiffAt_joint_referenceHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p hi).clm_comp contDiffAt_const)

local instance referenceFiniteHarmonicProductRadialSecondRemainderHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFiniteHarmonicProductRadialSecondRemainderHighOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

attribute [local irreducible] referenceFiniteHarmonicProductHighRadialFamily

def referenceFiniteHarmonicProductHighSecondRemainder
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (n : ℕ) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceFiniteHarmonicProductHighRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q (q,(y,t))) r

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_fixed
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteHarmonicProductHighSecondRemainder
