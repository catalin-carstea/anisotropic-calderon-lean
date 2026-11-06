import Calderon.ActualReferenceRotationCoefficientJets
import Calderon.ActualReferenceBoundaryCoefficientFamilies
import Calderon.NativeNormalCoefficientOrthogonalCovariance
import Calderon.NativeCoefficientMultiplierOrthogonalCovariance

/-! Expanded first in EXPANSION-actual-rotation-normal-multiplier-inverse-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


def referenceRotationNormalCoefficientJetsFamily (i j : Fin 3) :
    (ℝ × (ℝ × (R3 × ℝ))) → SmoothCoefficientJets 2 :=
  normalCoefficientJetsFamily (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2

def referenceRotationNormalBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)

lemma coefficientSmoothData_referenceRotationNormalCoefficientJetsFamily
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData
      (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j (θ,p)) =
    orthogonalSmoothPullback (coordinateRotationIsometry i j θ)
      (coefficientSmoothData (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)) := by
  apply Subtype.ext
  funext x
  change coefficientValue 2
      (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j (θ,p)) x =
    coefficientValue 2 (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)
      (coordinateRotationIsometry i j θ x)
  unfold referenceRotationNormalCoefficientJetsFamily referenceNormalCoefficientJetsFamily
    normalCoefficientJetsFamily
  rw [coefficientValue_commonSupportCoefficientFamily,coefficientValue_commonSupportCoefficientFamily]
  change (∑ k : Fin 3, ∑ l : Fin 3, x k *
    coordinateRotationPrincipalFamily i j a ((θ,p),x) k l * x l) =
      ∑ k : Fin 3, ∑ l : Fin 3, (coordinateRotationIsometry i j θ x) k *
        a (p,coordinateRotationIsometry i j θ x) k l * (coordinateRotationIsometry i j θ x) l
  rw [coordinateRotationPrincipalFamily_eq_orthogonal]
  exact normalCoefficient_orthogonal_covariance (coordinateRotationIsometry i j θ) (fun z => a (p,z)) x

lemma contDiff_referenceRotationNormalBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) :=
  contDiff_negativeHalf_normalCoefficientFamily hcalc hF hO hD τ0
    (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2

lemma referenceRotationNormalBoundaryMultiplierFamily_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ)) (u : SphereSobolev (-(1/2:ℝ))) :
    referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j (θ,p)
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ) u) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) :=
  nativeNegativeHalfCoefficientMulL_orthogonal_covariance hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceRotationNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j θ p) u

lemma referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible) :
    (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j (θ,p)).IsInvertible :=
  nativeNegativeHalfCoefficientMulL_orthogonal_isInvertible hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceRotationNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j θ p) hi

lemma referenceRotationNormalBoundaryMultiplierFamily_inverse_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible) (u : SphereSobolev (-(1/2:ℝ))) :
    (referenceRotationNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j (θ,p)).inverse
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ) u) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) (coordinateRotationIsometry i j θ)
      ((referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 p).inverse u) :=
  nativeNegativeHalfCoefficientMulL_inverse_orthogonal_covariance hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceRotationNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j θ p) hi u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceRotationNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalBoundaryMultiplierFamily_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalBoundaryMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalBoundaryMultiplierFamily_inverse_covariance
