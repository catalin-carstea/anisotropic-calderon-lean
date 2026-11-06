import Calderon.ActualReferenceRotationAdjointH2LiftFamily
import Calderon.NativeHalfCoefficientConormalTrace
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfCoefficientConormalTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceRotationAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0
    (nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA t))

lemma contDiff_referenceRotationAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA) := by
  unfold referenceRotationAdjointSharpConormalTraceFamily nativeHalfCoefficientConormalTraceL
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  have hm := contDiff_referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc 1 iA jA j i
  exact contDiff_const.clm_comp
    (contDiff_const.clm_comp (contDiff_const.clm_comp (hm.clm_comp contDiff_const)))

def referenceRotationAdjointHighConormalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceRotationAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).comp
    (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF iA jA t)

lemma contDiffOn_referenceRotationAdjointHighConormalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  (contDiff_referenceRotationAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 iA jA).contDiffOn.clm_comp
    (contDiffOn_referenceRotationAdjointH2LiftFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0 iA jA)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointHighConormalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointHighConormalFamily_invertibleLocus
