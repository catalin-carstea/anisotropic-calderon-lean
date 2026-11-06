import Calderon.ActualReferenceDegreeCommutatorHighBlock
import Calderon.SignedOperatorTaylorRemainder
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError
/-! Full upfront EXPANSION-v001.json precedes source. Actual canonical
bounded extension of the literal raw degree commutator, not an assumed norm. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


def referenceRadialDegreeCommutatorHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).toLinearMap.extendOfNorm
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap

def referenceRadialDegreeCommutatorHalfFirstFamily (q : ℝ) (y : R3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (deriv (fun r : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))) 0).toLinearMap.extendOfNorm
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap

def referenceRadialDegreeCommutatorHalfSecondRemainder (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (secondTaylorRemainder (fun t : ℝ => referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r).toLinearMap.extendOfNorm
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap


#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfFirstFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHalfSecondRemainder
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
