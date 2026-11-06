import Calderon.ActualReferenceDegreeCasimirCompatibleDataCore
import Calderon.PhysicalDegreeCasimirCompatibleRawGraph
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic PhysicalDegreeCasimirCompatibility
/-! Actual original data tuple and constraint membership. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceRadialRotationCommutatorMidpointFamily
  referenceAdjointMidpointAngleDerivativeFamily referenceLowerRadialEndpointFamily
  referenceSharpRadialTraceFamily sphereSobolevSingleL sphereSobolevCoefficientL
  sphereSobolevZeroEquiv sphereSobolevInclusionL

lemma referencePhysicalDegreeCasimirDataFamily_raw_high (p : ℝ × (R3 × ℝ)) :
    degreeRawHighDataL (referencePhysicalDegreeCasimirDataFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) =
      referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p := rfl

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referencePhysicalDegreeCasimirDataFamily_raw_high
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
