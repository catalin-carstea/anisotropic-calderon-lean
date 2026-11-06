import Calderon.ActualReferenceRotationRadialCompatibility
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Expanded first in EXPANSION-actual-rotation-lower-radial-dense-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationLowerRadialEndpointFamily_coordinate_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) :
    referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ) f) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f) := by
  apply lowerEndpoint_orthogonal_covariance_of_upper (coordinateRotationIsometry i j θ)
    (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p))
    (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (referenceOrthogonalSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (coordinateRotationIsometry i j θ) p)
  · intro u
    have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (referenceSharpRadialTraceFamily_lower_compatibility_of_isInvertible
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hStrong hWeak)
    exact h.symm
  · exact referenceRotationLowerRadialEndpointFamily_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak
  · exact referenceOrthogonalSharpRadialTraceFamily_orthogonal_covariance
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateRotationIsometry i j θ) p

lemma referenceRotationLowerRadialEndpointFamily_comp_coordinatePullback
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceRotationLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (θ,p)).comp
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) (coordinateRotationIsometry i j θ)) =
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)).comp
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) := by
  apply ContinuousLinearMap.ext
  intro f
  exact referenceRotationLowerRadialEndpointFamily_coordinate_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j θ p hNormal hStrong hWeak f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily_coordinate_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationLowerRadialEndpointFamily_comp_coordinatePullback
