import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceInvertibleWeakEndpointTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Fully expanded before source in EXPANSION-actual-radial-open-invertibility-locus-v001.json.
Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
lemma contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible) (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p := by
  have hNormalDiff := contDiff_referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hInvDiff : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) => (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t).inverse) p :=
    hNormal.contDiffAt_map_inverse.comp p hNormalDiff.contDiffAt
  have hWeakDiff := contDiffAt_referenceWeakConormalEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak
  have hTan : ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      ∑ j : Fin 3, (referenceTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j t).comp (sphereTangentialDerivativeL hF hO hD j)) p := by
    apply ContDiffAt.sum
    intro j hj
    exact (contDiff_referenceTangentBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j).contDiffAt.clm_comp contDiffAt_const
  exact hInvDiff.clm_comp (hWeakDiff.sub hTan)

lemma contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro p hp
  exact (contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.2.2 hp.2.1).contDiffWithinAt

lemma contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  intro p hp
  exact (contDiffAt_referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.1).contDiffWithinAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus
