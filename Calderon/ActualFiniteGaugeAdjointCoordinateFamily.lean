import Calderon.ActualFiniteGaugeAdjointRadialFamily
import Calderon.NativeFiniteHarmonicProductHighRotationGraph
import Calderon.NativeThreeHalfCoefficientCoordinateProduct

/-! The actual derivative taken after the coordinate product. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeFiniteHarmonicProductHighRotationL
  referenceFiniteGaugeAdjointRadialFamily sphereSobolevInclusionL
  sphereSobolevLinearCoordinateMulL sphereSobolevRotationL

variable {K0 : Set (ℝ × (R3 × ℝ))}

def referenceFiniteGaugeAdjointCoordinateFamily
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K0) (n : ℕ)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  -(∑ j : Fin 3, nativeFiniteHarmonicProductHighRotationL hcalc hF hO hD τ0 n
    (coefficientCoordinateJets Q j) j i) +
  referenceFiniteGaugeAdjointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (coefficientCoordinateJets Q i) p

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugeAdjointCoordinateFamily
