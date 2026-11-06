import Calderon.ActualReferenceTwoAngleAdjointH2LiftFamily
import Calderon.NativeHalfCoefficientConormalTrace
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
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

def referenceTwoAngleAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA kA lA : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0
    (nativePrincipalTransposeJets (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 iA jA kA lA t))

lemma contDiff_referenceTwoAngleAdjointSharpConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA kA lA : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA kA lA) := by
  unfold referenceTwoAngleAdjointSharpConormalTraceFamily nativeHalfCoefficientConormalTraceL
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  have hm := contDiff_referenceTwoAnglePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc 1 iA jA kA lA j i
  exact contDiff_const.clm_comp
    (contDiff_const.clm_comp (contDiff_const.clm_comp (hm.clm_comp contDiff_const)))

def referenceTwoAngleAdjointHighConormalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA kA lA : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (referenceTwoAngleAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA kA lA t).comp
    (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF iA jA kA lA t)

lemma contDiffOn_referenceTwoAngleAdjointHighConormalFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA kA lA : Fin 3) :
    ContDiffOn ℝ ∞ (referenceTwoAngleAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 iA jA kA lA)
      (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :=
  (contDiff_referenceTwoAngleAdjointSharpConormalTraceFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 iA jA kA lA).contDiffOn.clm_comp
    (contDiffOn_referenceTwoAngleAdjointH2LiftFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData
      hcalc hreg hF hO hD τ0 iA jA kA lA)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointSharpConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointHighConormalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleAdjointHighConormalFamily_invertibleLocus
