import Calderon.ActualFiniteGaugeAdjointCoordinateFamily
import Calderon.ActualJacobiCompactExtensionRoom
import Calderon.NativeThreeHalfUnitCoefficient
import Calderon.ActualHighAdjointMovingBoundaryFamilyDefinition

/-! The finite-gauge adjoint on the coordinate moving domain, with the actual Jacobi coefficient
order and the genuine adjoint. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeAdjointCoordinateFamily
  referenceFiniteGaugeAdjointRadialFamily referenceHighAdjointMovingBoundaryActionFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily nativeThreeHalfCoefficientMulL
  sphereSobolevInclusionL referenceStrongDriftFamily
  referenceRadiusHorizontalLogDerivative

variable {KG KJ : Set (ℝ × (R3 × ℝ))}
  (G : ReferenceGaugeNormalReciprocalRoom g L Φ a KG)
  (E : ReferenceJacobiCompactExtensionRoom
    (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) KJ)

def referenceFiniteGaugeAdjointMovingBoundaryFamily
    (n : ℕ) (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (R y)⁻¹ • referenceFiniteGaugeAdjointCoordinateFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(y,R y)) i +
  R y • (∑ j : Fin 3, referenceFiniteGaugeAdjointCoordinateFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (E.jets i j (q,(y,R y))) (q,(y,R y)) j) +
  referenceRadiusHorizontalLogDerivative g L q R y i • referenceFiniteGaugeAdjointRadialFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (unitSphereCoefficientJets 3) (q,(y,R y))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceFiniteGaugeAdjointMovingBoundaryFamily
