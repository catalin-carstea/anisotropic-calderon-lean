import Calderon.ActualAdjointHighCommonSupportGainTopologyTransferJointRegularity
import Calderon.ActualReferenceSmoothMultiplierJointTopology

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
open EnergyBridge ConnectionError SphereHarmonic

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

/-- RAW adjoint high multiplier commutator at the zero radial operator point. -/
def rawAdjointMultiplierZero (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) : Hi →L[ℝ] Hi :=
  referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q (q,(y,0))

/-- RAW primal Half multiplier commutator at the zero radial operator point. -/
def rawHalfMultiplierZero (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) : Half →L[ℝ] Half :=
  referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,0))

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
  (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
  (q : T → ℝ) (hq : ContDiff ℝ ∞ q) (y : T → R3) (hy : ContDiff ℝ ∞ y)

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily

include hq hy

lemma contDiffAt_rawAdjointMultiplierZero_commonSupport
    (t : T) (hp : (q t,(y t,(0 : ℝ))) ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (fun z : T => rawAdjointMultiplierZero
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
      (commonSupportCoefficientFamily 3 m hm Km hKm hmz z) (q z) (y z)) t := by
  have hPoint : ContDiff ℝ ∞ (fun z : T => ((q z,(y z,(0 : ℝ))),z)) :=
    (hq.prodMk (hy.prodMk contDiff_const)).prodMk contDiff_id
  have hJoint := contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 m hm Km hKm hmz
    (q t,(y t,0)) t hp
  have hComp := hJoint.comp (f := fun z : T => ((q z,(y z,(0 : ℝ))),z)) t hPoint.contDiffAt
  simpa only [Function.comp_def,rawAdjointMultiplierZero,rawHalfMultiplierZero] using hComp

lemma contDiffAt_rawHalfMultiplierZero_commonSupport
    (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 (q t) (y t,0)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc (q t,(y t,0))).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : T => rawHalfMultiplierZero
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
      (commonSupportCoefficientFamily 3 m hm Km hKm hmz z) (q z) (y z)) t := by
  have hPoint : ContDiff ℝ ∞ (fun z : T => ((q z,(y z,(0 : ℝ))),z)) :=
    (hq.prodMk (hy.prodMk contDiff_const)).prodMk contDiff_id
  have hJoint := contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
    (q t,(y t,0)) t hStrong hWeak
  have hComp := hJoint.comp (f := fun z : T => ((q z,(y z,(0 : ℝ))),z)) t hPoint.contDiffAt
  simpa only [Function.comp_def,rawAdjointMultiplierZero,rawHalfMultiplierZero] using hComp

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
