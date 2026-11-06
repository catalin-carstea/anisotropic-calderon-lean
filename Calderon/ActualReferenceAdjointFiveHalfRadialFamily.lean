import Calderon.ActualReferenceAdjointFiveHalfConormalFamily
import Calderon.ActualReferenceNormalFiveHalfInverseFamily
import Calderon.ActualReferenceAdjointFiveHalfLowerTerms
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceAdjointFiveHalfConormalFamily
  referenceNormalDriftFiveHalfMultiplierFamily referenceTangentialAdjointFiveHalfFamily
  referenceNormalFiveHalfMultiplierFamily

def referenceAdjointFiveHalfRadialFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (referenceAdjointFiveHalfConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p +
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (referenceNormalDriftFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    referenceTangentialAdjointFiveHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse

lemma contDiffOn_referenceAdjointFiveHalfRadialFamily_invertibleLocus
    (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceAdjointFiveHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceAdjointFiveHalfRadialFamily
  exact ((contDiffOn_referenceAdjointFiveHalfConormalFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0).add
    (contDiffOn_const.clm_comp (contDiff_referenceNormalDriftFiveHalfMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn)).sub
      (contDiff_referenceTangentialAdjointFiveHalfFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn |>.clm_comp
        (contDiff_referenceNormalFiveHalfMultiplierFamily_inverse
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
