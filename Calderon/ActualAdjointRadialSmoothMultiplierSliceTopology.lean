import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.ActualReferenceSmoothMultiplierJointTopology
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma contDiffAt_referenceAdjointHalfRadialFamily_radialSlice
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (tau : ℝ)
    (hp : (q,(y,tau)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) tau := by
  have hJoint := (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
      ((isOpen_referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hComp := hJoint.comp (f := fun z : ℝ => (q,(y,z))) tau
    (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  simpa only [Function.comp_def] using hComp

variable
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
  (hmz : ∀ t x, x ∉ Km → m (t,x)=0)

lemma contDiffAt_referenceSmoothMultiplierBoundaryCommutator_radialSlice
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3) (tau : ℝ) (t : T)
    (hp : (q,(y,tau)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,z))) tau := by
  have hJoint := contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
      (q,(y,tau)) t hp.1 hp.2.1
  have hComp := hJoint.comp (f := fun z : ℝ => ((q,(y,z)),t)) tau
    ((contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)).prodMk contDiffAt_const)
  exact hComp

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointHalfRadialFamily_radialSlice
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothMultiplierBoundaryCommutator_radialSlice
