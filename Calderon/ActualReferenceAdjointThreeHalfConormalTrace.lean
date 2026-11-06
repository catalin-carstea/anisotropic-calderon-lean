import Calderon.ActualReferenceAdjointH3Operator
import Calderon.NativeH3CoefficientConormalTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3CoefficientConormalTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- The H³-to-H³ᐟ² conormal trace for the SAME transposed reference
principal field. The full adjoint solution is supplied separately. -/
def referenceAdjointThreeHalfConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    BallSobolev 3 →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0
    (fun i j => referenceJointPrincipalJetsFamilyThree
      g L y0 Φ B ε C ρ H a w hData p j i)

lemma contDiff_referenceAdjointThreeHalfConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceAdjointThreeHalfConormalTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceAdjointThreeHalfConormalTraceFamily
    nativeThreeHalfCoefficientConormalTraceL
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  have hm : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 2
      (referenceJointPrincipalJetsFamilyThree g L y0 Φ B ε C ρ H a w hData p j i)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 2
    (fun q => a q j i)
    (contDiff_pi.mp (contDiff_pi.mp
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 j) i)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun p x hx => by rw [(jointReferenceStrongCoefficient_data
      g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p x hx]; rfl)
  exact contDiff_const.clm_comp
    (contDiff_const.clm_comp (hm.clm_comp contDiff_const))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
