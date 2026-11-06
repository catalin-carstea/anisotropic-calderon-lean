import Calderon.ActualNativeMovingAdjointMixedJDictionary

/-! Actual ordered mixed zero/first expression, same finite-J graph and bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic AngularShiftGraph
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  sphereSobolevAngularCoordinateTransposeL referenceNativeMovingAdjointParametricCorrection
  referenceNativeMovingAdjointParametricJ referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL

def referenceNativeMovingAdjointHighMixedCorrection
    (g2 : MatrixField) (q : ℝ) (y : R3) (ell : R3 →L[ℝ] ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (∑ i : Fin 3, ∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L q y i j •
    ((referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i).comp
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (3/2 : ℝ) ((q,y),ell) j) +
    (referenceNativeMovingAdjointParametricCorrection hF hO hD g L (1/2 : ℝ) ((q,y),ell) i).comp
      (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j))) +
  ∑ i : Fin 3, normalizedSecondDriftFrameJoint g g2 L i (q,y) •
    referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) i


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointHighMixedCorrection
