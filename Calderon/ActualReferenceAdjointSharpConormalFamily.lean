import Calderon.ActualReferenceAdjointH2LiftFamily
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

def referenceAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0
    (nativePrincipalTransposeJets (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))

lemma contDiff_referenceAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0) := by
  unfold referenceAdjointSharpConormalTraceFamily nativeHalfCoefficientConormalTraceL
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
    (fun q => a q j i)
    (contDiff_pi.mp (contDiff_pi.mp
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 j) i)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun p x hx => by rw [(jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p x hx]; rfl)
  exact contDiff_const.clm_comp
    (contDiff_const.clm_comp (contDiff_const.clm_comp (hm.clm_comp contDiff_const)))

def referenceAdjointHighConormalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
    (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)

lemma contDiffOn_referenceAdjointHighConormalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  (contDiff_referenceAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0).contDiffOn.clm_comp
    (contDiffOn_referenceAdjointH2LiftFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighConormalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointHighConormalFamily_invertibleLocus
