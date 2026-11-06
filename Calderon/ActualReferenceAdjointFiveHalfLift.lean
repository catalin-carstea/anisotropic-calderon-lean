import Calderon.ActualReferenceAdjointH3StrongInverse
import Calderon.ActualReferenceAdjointH3OperatorSmooth
import Calderon.NativeFiveHalfHarmonicCoherence
import Calderon.StrongHarmonicProjection

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeFiveHalfHarmonicLift
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Full adjoint H5/2 boundary data to H3 bulk solution, using the SAME
order-one full adjoint and its derived strong Dirichlet inverse. -/
def referenceAdjointFiveHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (5/2:ℝ) →L[ℝ] BallSobolev 3 :=
  (strongHarmonicProjectionL 1
    (referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p)).comp
    (harmonicLiftCompletion hF)

lemma referenceAdjointFiveHalfLiftFamily_strong_kernel
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (5/2:ℝ)) :
    referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc p
        (referenceAdjointFiveHalfLiftFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF p f) = 0 := by
  exact strongHarmonicProjectionL_equation 1 _
    (referenceAdjointStrongDirichletFamilyOne_isInvertible
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hOriginal)
    (harmonicLiftCompletion hF f)

lemma contDiffOn_referenceAdjointFiveHalfLiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞
      (referenceAdjointFiveHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF)
      (referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  let Q := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hi : ∀ p ∈ Q,
      ((referenceAdjointOrdinaryStrongFamilyOne
        g L y0 Φ B ε C ρ H a w hData hcalc p).comp
        (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible := by
    intro p hp
    exact referenceAdjointStrongDirichletFamilyOne_isInvertible
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg p hp.2.1
  have hP := contDiffOn_strongHarmonicProjectionL 1
    (referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc) Q
    (contDiff_referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc).contDiffOn hi
  unfold referenceAdjointFiveHalfLiftFamily
  exact hP.clm_comp contDiffOn_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
