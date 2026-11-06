import Calderon.ActualReferenceAdjointFiveHalfLift
import Calderon.ActualReferenceAdjointThreeHalfConormalTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- SAME full formal-adjoint D2N endpoint on H5/2 data. The solution is
obtained with the complete order-one adjoint, then the transposed principal
conormal is traced at order H3/2. -/
def referenceAdjointFiveHalfConormalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (referenceAdjointThreeHalfConormalTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (referenceAdjointFiveHalfLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF p)

lemma contDiffOn_referenceAdjointFiveHalfConormalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞
      (referenceAdjointFiveHalfConormalFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
      (referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  (contDiff_referenceAdjointThreeHalfConormalTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffOn.clm_comp
    (contDiffOn_referenceAdjointFiveHalfLiftFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
