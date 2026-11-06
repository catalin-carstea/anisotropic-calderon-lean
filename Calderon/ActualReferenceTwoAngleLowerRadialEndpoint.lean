import Calderon.ActualReferenceTwoAngleLowerRadialEndpointCore
import Calderon.ActualReferenceTwoAngleWeakConormalTopology

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

lemma contDiffAt_referenceTwoAngleLowerRadialEndpointFamily_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginalNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 t.2.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) t := by
  have hNormal := referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t.1 t.2.1 t.2.2 hOriginalNormal
  have hn := contDiff_referenceTwoAngleNormalBoundaryMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l
  have hinv : ContDiffAt ℝ ∞ (fun z => (referenceTwoAngleNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l z).inverse) t :=
    hNormal.contDiffAt_map_inverse.comp t hn.contDiffAt
  have hw := contDiffAt_referenceTwoAngleWeakConormalEndpointFamily_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t hWeak
  have ht : ContDiffAt ℝ ∞ (fun z => ∑ d : Fin 3,
      (referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j k l d z).comp (sphereTangentialDerivativeL hF hO hD d)) t := by
    apply ContDiffAt.sum
    intro d hl
    exact (contDiff_referenceTwoAngleTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l d).contDiffAt.clm_comp
        (contDiffAt_const (c := sphereTangentialDerivativeL hF hO hD d))
  exact hinv.clm_comp (hw.sub ht)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleLowerRadialEndpointFamily_of_original
