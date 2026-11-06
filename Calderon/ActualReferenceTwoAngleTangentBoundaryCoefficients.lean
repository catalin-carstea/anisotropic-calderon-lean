import Calderon.ActualReferenceTwoAngleCoefficientJets
import Calderon.ActualReferenceTwoAngleNormalCovariance
import Calderon.SphereSobolevTangentialDerivative

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-tangent-pairing-partition-v099.md. Exact coefficient partition. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTwoAngleTangentCoefficientJetsFamily (i j k l d : Fin 3) :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → SmoothCoefficientJets 2 :=
  tangentCoefficientJetsFamily (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 d

def referenceTwoAngleTangentBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l d : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l d t)

lemma coefficientSmoothData_referenceTwoAngleNormalJets_eq_boundaryData
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    coefficientSmoothData (referenceTwoAngleNormalCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j k l t) =
    boundaryNormalCoefficientData
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) :=
  coefficientSmoothData_normalCoefficientJetsFamily (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t

lemma coefficientSmoothData_referenceTwoAngleTangentJets_eq_boundaryData
    (i j k l d : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    coefficientSmoothData (referenceTwoAngleTangentCoefficientJetsFamily
      g L y0 Φ B ε C ρ H a w hData i j k l d t) =
    boundaryTangentCoefficientData
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) d :=
  coefficientSmoothData_tangentCoefficientJetsFamily (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 d t

lemma contDiff_referenceTwoAngleTangentBoundaryMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l d : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l d) :=
  contDiff_negativeHalf_tangentCoefficientFamily hcalc hF hO hD τ0
    (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 d

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentCoefficientJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTangentBoundaryMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceTwoAngleNormalJets_eq_boundaryData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientSmoothData_referenceTwoAngleTangentJets_eq_boundaryData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleTangentBoundaryMultiplierFamily
