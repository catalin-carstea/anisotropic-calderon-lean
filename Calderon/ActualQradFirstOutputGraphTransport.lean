import Calderon.ActualQradSectionContinuityAndHighGraph
import Calderon.ActualFinitePairedRadialRemainderClosedSections
import Calderon.ActualOriginalPiQradReferenceProfile
import Calderon.ActualFinitePairedRadialRemainderSections
import Calderon.ActualFinitePhysicalWeakSquaredNorm
import Calderon.ActualQradJointCoefficientCaps
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderTopologyCoercivity

/-! Original-Pi Qrad self row as a difference of two SEPARATELY integrable weighted squared norms
(author-only successor, v010). Complete expansion: output/MATHEMATICS.md (N0–N7), written before
these declarations. Imports the proposed parent `Calderon.ActualOriginalPiQradReferenceProfile`
without redoing it. No compiler was run; no acceptance is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
open ActualFiniteHarmonicCore ActualFiniteHarmonicModel ReferenceDensityBounds ConformalDepth
  ReferenceWeightedApproximation

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  commonSupportCoefficientFamily referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier referenceDensityPrincipalFrameCoefficient finiteCoreSobolevLift
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder

attribute [local instance] adjacentGainThreeHalfComplete adjacentGainHalfComplete adjacentGainNegativeHalfComplete adjacentGainHighHighComplete adjacentGainHighHalfComplete adjacentGainHalfHalfComplete adjacentGainHalfNegComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCL" => referenceSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-! ### N3 (L1): continuity patch — continuous on a closed set, input vanishing off it. -/

attribute [local irreducible] sphereSobolevPartialSum qradSignedWeakSelfExpression qradFourIndexWeakForm

theorem referenceNative_finite_first_output_graph_transport
    (n : ℕ) (f : Hi) (hcut : sphereSobolevPartialSum (3/2 : ℝ) n f = f)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ)
    (etaP etaA : Hi)
    (hP : Ihi etaP = (secondTaylorRemainder (fun s : ℝ => referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r)
        (NMH Q (sphereSobolevPartialSum (3/2 : ℝ) n f)))
    (hA : Ihi etaA = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r)
        (NMH Q (sphereSobolevPartialSum (3/2 : ℝ) n f)))
    (hG : Ihi (GHr Q q y r f) = Sh q y r (NMH Q f) - NML (smoothMultiplierLowerJets Q) (Sh q y r f))
    :
    Ihi etaA = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (NMH Q f) ∧
    Ihi (etaP - GHr Q q y r f) = NML (smoothMultiplierLowerJets Q) (Sh q y r f) := by
  have hP' : Ihi etaP = Sh q y r (NMH Q f) := by
    have hc := congrArg (fun v : Hi => (secondTaylorRemainder (fun s : ℝ => referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r) (NMH Q v)) hcut
    simpa only [referenceSharpRadialTraceSecondRemainder] using hP.trans hc
  have hA' : Ihi etaA = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (NMH Q f) :=
    hA.trans (congrArg (fun v : Hi =>
      (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (NMH Q v)) hcut)
  have hL : Ihi (etaP - GHr Q q y r f) = NML (smoothMultiplierLowerJets Q) (Sh q y r f) := by
    exact ((Ihi).map_sub etaP (GHr Q q y r f)).trans
      ((congrArg₂ (fun x z : Half => x-z) hP' hG).trans (sub_sub_cancel _ _))
  exact ⟨hA',hL⟩

theorem referencePi_finite_first_output_graph_transport
    (n : ℕ) (f : Hi) (hcut : sphereSobolevPartialSum (3/2 : ℝ) n f = f)
    (i : Fin 3) (t : Tpar) (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ)
    (etaP etaA : Hi)
    (hP : Ihi etaP = (secondTaylorRemainder (fun s : ℝ => referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r)
        (NMH Q (sphereSobolevPartialSum (3/2 : ℝ) n f)))
    (hA : Ihi etaA = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r)
        (NMH Q (sphereSobolevPartialSum (3/2 : ℝ) n f)))
    (hG : Ihi (GHr Q q y r f) = Sh q y r (NMH Q f) - NML (smoothMultiplierLowerJets Q) (Sh q y r f))
    (hMH : NMH Q = PiH i t) (hML : NML (smoothMultiplierLowerJets Q) = PiL i t) :
    Ihi etaA = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (PiH i t f) ∧
    Ihi (etaP - GHr Q q y r f) = PiL i t (Sh q y r f) := by
  have h := referenceNative_finite_first_output_graph_transport
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    n f hcut Q q y r etaP etaA hP hA hG
  refine ⟨h.1.trans ?_,h.2.trans ?_⟩
  · exact congrArg (fun Aop : Hi →L[ℝ] Hi =>
      (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (Aop f)) hMH
  · exact congrArg (fun Aop : Half →L[ℝ] Half => Aop (Sh q y r f)) hML

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
