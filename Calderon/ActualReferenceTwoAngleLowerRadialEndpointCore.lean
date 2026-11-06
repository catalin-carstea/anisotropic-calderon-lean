import Calderon.ActualReferenceTwoAngleTangentBoundaryCoefficients
import Calderon.ActualReferenceTwoAngleWeakConormalCore
import Calderon.SphereSobolevTangentialDerivative

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

def referenceTwoAngleLowerRadialEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t).inverse.comp
      (referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t -
        ∑ d : Fin 3, (referenceTwoAngleTangentBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l d t).comp
            (sphereTangentialDerivativeL hF hO hD d))

lemma referenceTwoAngleLowerRadialEndpointFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f : SphereSobolev (1/2:ℝ)) :
    referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t f =
    (referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j k l t).inverse
      (referenceTwoAngleWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f -
        ∑ d : Fin 3, referenceTwoAngleTangentBoundaryMultiplierFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l d t
            (sphereTangentialDerivativeL hF hO hD d f)) := by
  simp only [referenceTwoAngleLowerRadialEndpointFamily,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleLowerRadialEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleLowerRadialEndpointFamily_apply
