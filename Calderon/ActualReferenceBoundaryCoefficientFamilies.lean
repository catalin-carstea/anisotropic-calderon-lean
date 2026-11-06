import Calderon.NativeNormalCoefficientInverseFamily
import Calderon.ActualJointReferenceCoefficientData

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Fully expanded before source in EXPANSION-actual-reference-lower-radial-endpoint-v001.json.
Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
def referenceNormalCoefficientJetsFamily : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 2 :=
  normalCoefficientJetsFamily a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1

def referenceTangentCoefficientJetsFamily (j : Fin 3) : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 2 :=
  tangentCoefficientJetsFamily a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 j

def referenceNormalBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)

def referenceTangentBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p)

lemma coefficientSmoothData_referenceNormalCoefficientJetsFamily (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p) = boundaryNormalCoefficientData
      (commonSupportMatrixFamily 2 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p) :=
  coefficientSmoothData_normalCoefficientJetsFamily a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p

lemma coefficientSmoothData_referenceTangentCoefficientJetsFamily (j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData (referenceTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData j p) = boundaryTangentCoefficientData
      (commonSupportMatrixFamily 2 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p) j :=
  coefficientSmoothData_tangentCoefficientJetsFamily a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 j p

lemma contDiff_referenceNormalBoundaryMultiplierFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_negativeHalf_normalCoefficientFamily hcalc hF hO hD τ0 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1

lemma contDiff_referenceTangentBoundaryMultiplierFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (j : Fin 3) :
    ContDiff ℝ ∞ (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j) :=
  contDiff_negativeHalf_tangentCoefficientFamily hcalc hF hO hD τ0 a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 j

lemma referenceNormalBoundaryMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam) :
    (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible :=
  nativeNegativeHalf_normalCoefficientFamily_isInvertible hcalc hF hO hD τ0
    a (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 (closedBall (0 : R3) 3)
      (isCompact_closedBall _ _) (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p lam Lam hUE

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceNormalCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTangentBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalBoundaryMultiplierFamily_isInvertible
