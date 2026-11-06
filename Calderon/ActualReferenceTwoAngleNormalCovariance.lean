import Calderon.ActualReferenceTwoAngleCoefficientData
import Calderon.ActualReferenceRotationNormalCoefficient

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-ordinary-normal-covariance-v004.md. ORDINARY principal
normal coefficient, distinct from exponential-gauge alpha. E=R_inner R_outer. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open SphereHarmonic NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies
  SmoothSphereRotation

def referenceTwoAngleNormalCoefficientJetsFamily (i j k l : Fin 3) :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → SmoothCoefficientJets 2 :=
  normalCoefficientJetsFamily (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2

def referenceTwoAngleNormalBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)

lemma coefficientSmoothData_referenceTwoAngleNormal_pullback
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData (referenceTwoAngleNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j k l (θ,(φ,p))) =
    orthogonalSmoothPullback (coordinateRotationIsometry i j θ)
      (coefficientSmoothData (referenceRotationNormalCoefficientJetsFamily
        g L y0 Φ B ε C ρ H a w hData k l (φ,p))) := by
  apply Subtype.ext
  funext x
  change coefficientValue 2 (referenceTwoAngleNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j k l (θ,(φ,p))) x =
    coefficientValue 2 (referenceRotationNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData k l (φ,p)) (coordinateRotationIsometry i j θ x)
  unfold referenceTwoAngleNormalCoefficientJetsFamily referenceRotationNormalCoefficientJetsFamily
    normalCoefficientJetsFamily
  rw [coefficientValue_commonSupportCoefficientFamily,coefficientValue_commonSupportCoefficientFamily]
  change (∑ d : Fin 3, ∑ e : Fin 3, x d *
    referenceTwoAnglePrincipalFamily a i j k l ((θ,(φ,p)),x) d e * x e) =
      ∑ d : Fin 3, ∑ e : Fin 3, (coordinateRotationIsometry i j θ x) d *
        coordinateRotationPrincipalFamily k l a ((φ,p),coordinateRotationIsometry i j θ x) d e *
          (coordinateRotationIsometry i j θ x) e
  unfold referenceTwoAnglePrincipalFamily
  rw [coordinateRotationPrincipalFamily_eq_orthogonal]
  exact normalCoefficient_orthogonal_covariance (coordinateRotationIsometry i j θ)
    (fun z => coordinateRotationPrincipalFamily k l a ((φ,p),z)) x

lemma contDiff_referenceTwoAngleNormalBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :=
  contDiff_negativeHalf_normalCoefficientFamily hcalc hF hO hD τ0
    (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2

lemma referenceTwoAngleNormalBoundaryMultiplierFamily_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (u : SphereSobolev (-(1/2 : ℝ))) :
    referenceTwoAngleNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)
        (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ) u)) =
    sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ)
        (referenceNormalBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u)) := by
  have hOuter := nativeNegativeHalfCoefficientMulL_orthogonal_covariance hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceTwoAngleNormal_pullback
      g L y0 Φ B ε C ρ H a w hData i j k l θ φ p)
    (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ) u)
  have hInner := referenceRotationNormalBoundaryMultiplierFamily_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p u
  exact hOuter.trans (congrArg
    (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)) hInner)

lemma referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible) :
    (referenceTwoAngleNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))).IsInvertible := by
  have hInner := referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hi
  exact nativeNegativeHalfCoefficientMulL_orthogonal_isInvertible hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceTwoAngleNormal_pullback
      g L y0 Φ B ε C ρ H a w hData i j k l θ φ p) hInner

lemma referenceTwoAngleNormalBoundaryMultiplierFamily_inverse_covariance
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (θ φ : ℝ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (u : SphereSobolev (-(1/2 : ℝ))) :
    (referenceTwoAngleNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l (θ,(φ,p))).inverse
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)
        (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ) u)) =
    sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ)
        ((referenceNormalBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse u)) := by
  have hInnerInv := referenceRotationNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hi
  have hOuter := nativeNegativeHalfCoefficientMulL_inverse_orthogonal_covariance hcalc hF hO hD τ0
    (coordinateRotationIsometry i j θ) _ _
    (coefficientSmoothData_referenceTwoAngleNormal_pullback
      g L y0 Φ B ε C ρ H a w hData i j k l θ φ p) hInnerInv
    (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry k l φ) u)
  have hInner := referenceRotationNormalBoundaryMultiplierFamily_inverse_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 k l φ p hi u
  exact hOuter.trans (congrArg
    (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) (coordinateRotationIsometry i j θ)) hInner)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceTwoAngleNormal_pullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalBoundaryMultiplierFamily_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalBoundaryMultiplierFamily_inverse_covariance
