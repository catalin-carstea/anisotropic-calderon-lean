import Calderon.ActualReferenceAdjointConormalCompatibility
import Calderon.ActualReferenceNormalDriftEndpointFamilies
import Calderon.ActualReferenceTangentialAdjointEndpointFamilies
import Calderon.ActualReferenceNormalHalfInverseFamily
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

def referenceAdjointThreeHalfRadialFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p +
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse

def referenceAdjointHalfRadialFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (referenceAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF p +
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse

lemma contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus (hreg : FixedDirichletRegularity) :
    ContDiffOn ℝ ∞ (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceAdjointThreeHalfRadialFamily
  exact ((contDiffOn_referenceAdjointHighConormalFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0).add
    (contDiffOn_const.clm_comp (contDiff_referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn)).sub
      (contDiff_referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn |>.clm_comp
        (contDiff_referenceNormalThreeHalfMultiplierFamily_inverse g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn

lemma contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus :
    ContDiffOn ℝ ∞ (referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceAdjointHalfRadialFamily
  exact ((contDiffOn_referenceAdjointWeakConormalEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).add
    (contDiffOn_const.clm_comp (contDiff_referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn)).sub
      (contDiff_referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn |>.clm_comp
        (contDiff_referenceNormalHalfMultiplierFamily_inverse g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointThreeHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHalfRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
