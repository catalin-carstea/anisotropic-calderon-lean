import Calderon.ActualHighRadialCommutatorGain
import Calderon.ActualAdjointHighCommonSupportSecondTaylorSmoothnessCoercivity
import Calderon.ActualReferenceRadialAdjointSharpJointSmoothnessCoercivity
import Calderon.ActualReferenceSmoothMultiplierSecondTaylorSmoothness
import Calderon.NativeSmoothMultiplierCommonSupportJets

/-! v005 successor (author-only, UNCOMPILED): actual high/low adjacent gained commutators,
joint C^∞ and uniform op-norm caps on one fixed radial box.
Mathematics: output/MATHEMATICS.md (A1-A5), written before this file.
Parent `Calderon.ActualHighRadialCommutatorGain` = exact v004 candidate source (Root qualifies).
No sorry/admit/axiom/opaque/native_decide. Local instances are only the Prop-valued
`CompleteSpace` facts for existing carriers, as in the supplied owners. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder

local instance adjacentGainThreeHalfComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjacentGainHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjacentGainNegativeHalfComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjacentGainHighHighComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance adjacentGainHighHalfComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance adjacentGainHalfHalfComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance adjacentGainHalfNegComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by infer_instance

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
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "KbH" => referenceRadialAdjointSharpSecondCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "KbL" => referenceRadialAdjointSharpSecondCommutator
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "NMH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NML" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NMN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "RAH" => referenceAdjointThreeHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "RAL" => referenceAdjointHalfRadialFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCL" => referenceSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "BCA" => referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-! ### A1. The named actual adjacent maps (literally the two sides of v004 H13). -/

/-- Actual HIGH adjacent gained commutator `Hi → Half` (five-term H8/H13 expression). -/
def referenceAdjacentGainedCommutatorHigh (Qi Qk : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r : ℝ) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  -((KbH q y r).comp ((NMH Qi).comp (NMH Qk))) -
    (Sh q y r).comp ((secondTaylorRemainder (fun s : ℝ => BCA Qi (q,(y,s))) r).comp (NMH Qk)) -
    (secondTaylorRemainder (fun s : ℝ => BCL Qi (q,(y,s))) r).comp
      ((secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp (NMH Qk)) +
    (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp ((GHr Qi q y r).comp (NMH Qk)) +
    (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp ((NMH Qi).comp (GHr Qk q y r))

/-- Actual LOW adjacent gained commutator `Half → Neg`:
`-MN_i Kbar ML_k + MN_i Tl G_k - GN_i MN_k Sl`, `GN_i = -realHalfOperatorAdjointL G_i` (MINUS kept). -/
def referenceAdjacentGainedCommutatorLow (Qi Qk : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r : ℝ) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  -((NMN (smoothMultiplierLowerJets Qi)).comp ((KbL q y r).comp (NML (smoothMultiplierLowerJets Qk)))) +
    (NMN (smoothMultiplierLowerJets Qi)).comp
      ((secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r).comp
        (secondTaylorRemainder (fun s : ℝ => BCL Qk (q,(y,s))) r)) -
    (-(realHalfOperatorAdjointL (secondTaylorRemainder (fun s : ℝ => BCL Qi (q,(y,s))) r))).comp
      ((NMN (smoothMultiplierLowerJets Qk)).comp (Sl q y r))

local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

attribute [local irreducible] referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

/-! ### A2. Graph for the named maps (parent H13, per family). -/

theorem exists_reference_commonRadius_referenceAdjacentGainedCommutator_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
    (hmz : ∀ t x, x ∉ Km → m (t,x) = 0) (t : T) (Qk : SmoothCoefficientJets 3) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : SphereSobolev (3/2 : ℝ),
          Jlo (CH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) Qk q y r u) =
            CL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) Qk q y r (Ihi u) := by
  obtain ⟨d,hd,hdρ,hG⟩ := exists_reference_commonRadius_adjacentGainedCommutator_high_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel m hm Km hKm hmz t Qk
  refine ⟨d,hd,hdρ,?_⟩
  intro q hq y hy r hr u
  unfold referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  exact hG q hq y hy r hr u

/-! ### A3(i). Joint C^∞ of the actual lower adjoint radial remainder `Tl`. -/

lemma contDiffAt_referenceAdjointHalfRadialSecondRemainder_joint_of_segment
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => secondTaylorRemainder
      (fun t : ℝ => RAL (z.1,(z.2.1,t))) z.2.2) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun z =>
    RAL (z.1.1,(z.1.2,z.2))
  let U : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hΩ := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hU : IsOpen U :=
    hΩ.preimage (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFU : ContDiffOn ℝ ∞ F U := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hz
    have hRaw := (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt (hΩ.mem_nhds hi)
    exact (hRaw.comp (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z
      (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ((q,y),r) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F U hU hFU (q,y) r hSegment
  have hOut := hR.comp
    (f := fun z : ℝ × (R3 × ℝ) => ((z.1,z.2.1),z.2.2)) (q,(y,r))
      ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  simpa only [Function.comp_def,F] using hOut

/-! ### A3. Joint C^∞ of the two ACTUAL adjacent maps in (p,(ti,tk)), coefficients frozen. -/

theorem contDiffAt_referenceAdjacentGainedCommutatorHigh_of_segment
    (hreg : FixedDirichletRegularity)
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (mi : T × R3 → ℝ) (hmi : ContDiff ℝ ∞ mi) (Ki : Set R3) (hKi : IsCompact Ki)
    (hmiz : ∀ t x, x ∉ Ki → mi (t,x) = 0)
    (mk : T × R3 → ℝ) (hmk : ContDiff ℝ ∞ mk) (Kk : Set R3) (hKk : IsCompact Kk)
    (hmkz : ∀ t x, x ∉ Kk → mk (t,x) = 0)
    (q : ℝ) (y : R3) (r : ℝ) (ti tk : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
        (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) := by
  have hHighLoc : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc := by
    intro θ hθ
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hHigh θ hθ
  have hPi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
      ((q,(y,r)),(ti,tk)) := contDiffAt_fst.prodMk contDiffAt_snd.fst
  have hPk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.2))
      ((q,(y,r)),(ti,tk)) := contDiffAt_fst.prodMk contDiffAt_snd.snd
  -- (a) high Kbar (v004 H11)
  have hKb : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => KbH z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceRadialAdjointSharpSecondCommutatorHigh_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg q y r hSegment hHigh).comp
        (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1) ((q,(y,r)),(ti,tk)) contDiffAt_fst
  -- (b) native 3/2 common-support multipliers
  have hMi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      NMH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)) ((q,(y,r)),(ti,tk)) :=
    (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      mi hmi Ki hKi hmiz).comp_contDiffAt ((q,(y,r)),(ti,tk)) contDiffAt_snd.fst
  have hMk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      NMH (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)) ((q,(y,r)),(ti,tk)) :=
    (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      mk hmk Kk hKk hmkz).comp_contDiffAt ((q,(y,r)),(ti,tk)) contDiffAt_snd.snd
  -- (c) Sh and Th
  have hPair := contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hSh : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => Sh z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) := hPair.1.comp
        (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1) ((q,(y,r)),(ti,tk)) contDiffAt_fst
  have hTh : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) := hPair.2.comp
        (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1) ((q,(y,r)),(ti,tk)) contDiffAt_fst
  -- (d) high adjoint multiplier remainder, coefficient frozen (supplied owner)
  have hGA : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ =>
        BCA (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1) (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceAdjointHighCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 mi hmi Ki hKi hmiz q y r ti
        hHighLoc).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
          ((q,(y,r)),(ti,tk)) hPi
  -- (e) lower multiplier remainder, coefficient frozen
  have hGi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ =>
        BCL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1) (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 mi hmi Ki hKi hmiz q y r ti
        hSegment).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
          ((q,(y,r)),(ti,tk)) hPi
  -- (f) high multiplier remainder, coefficient frozen
  have hGHi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      GHr (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1) z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
      g L y0 Φ B ε C ρ H a w hData mi hmi Ki hKi hmiz hcalc hF hO hD τ0 q y r ti
        hHigh).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
          ((q,(y,r)),(ti,tk)) hPi
  have hGHk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      GHr (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
      g L y0 Φ B ε C ρ H a w hData mk hmk Kk hKk hmkz hcalc hF hO hD τ0 q y r tk
        hHigh).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.2))
          ((q,(y,r)),(ti,tk)) hPk
  unfold referenceAdjacentGainedCommutatorHigh
  exact ((((hKb.clm_comp (hMi.clm_comp hMk)).neg.sub
      (hSh.clm_comp (hGA.clm_comp hMk))).sub
      (hGi.clm_comp (hTh.clm_comp hMk))).add
      (hTh.clm_comp (hGHi.clm_comp hMk))).add
      (hTh.clm_comp (hMi.clm_comp hGHk))

theorem contDiffAt_referenceAdjacentGainedCommutatorLow_of_segment
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (mi : T × R3 → ℝ) (hmi : ContDiff ℝ ∞ mi) (Ki : Set R3) (hKi : IsCompact Ki)
    (hmiz : ∀ t x, x ∉ Ki → mi (t,x) = 0)
    (mk : T × R3 → ℝ) (hmk : ContDiff ℝ ∞ mk) (Kk : Set R3) (hKk : IsCompact Kk)
    (hmkz : ∀ t x, x ∉ Kk → mk (t,x) = 0)
    (q : ℝ) (y : R3) (r : ℝ) (ti tk : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
        (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) := by
  have hPi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
      ((q,(y,r)),(ti,tk)) := contDiffAt_fst.prodMk contDiffAt_snd.fst
  have hPk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.2))
      ((q,(y,r)),(ti,tk)) := contDiffAt_fst.prodMk contDiffAt_snd.snd
  -- (g) lower native multipliers through the exact order-2 common-support jets
  have hNi' : ContDiff ℝ ∞ (fun t : T =>
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz t))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 mi hmi Ki hKi hmiz
  have hNk' : ContDiff ℝ ∞ (fun t : T =>
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz t))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 mk hmk Kk hKk hmkz
  have hLk' : ContDiff ℝ ∞ (fun t : T =>
      NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz t))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 mk hmk Kk hKk hmkz
  have hNi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)))
      ((q,(y,r)),(ti,tk)) := hNi'.comp_contDiffAt ((q,(y,r)),(ti,tk)) contDiffAt_snd.fst
  have hNk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)))
      ((q,(y,r)),(ti,tk)) := hNk'.comp_contDiffAt ((q,(y,r)),(ti,tk)) contDiffAt_snd.snd
  have hLk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)))
      ((q,(y,r)),(ti,tk)) := hLk'.comp_contDiffAt ((q,(y,r)),(ti,tk)) contDiffAt_snd.snd
  -- (h) lower Kbar and Sl
  have hKL : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => KbL z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceRadialAdjointSharpSecondCommutator_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel (q,(y,r))
        hSegment).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1)
          ((q,(y,r)),(ti,tk)) contDiffAt_fst
  have hSl : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) => Sl z.1.1 z.1.2.1 z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceLowerRadialTraceSecondRemainder_joint_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) hSegment).comp
        (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1) ((q,(y,r)),(ti,tk)) contDiffAt_fst
  -- (i) Tl
  have hTl : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ => RAL (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceAdjointHalfRadialSecondRemainder_joint_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment).comp
        (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => z.1) ((q,(y,r)),(ti,tk)) contDiffAt_fst
  -- (e) lower multiplier remainders, coefficients frozen
  have hGi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ =>
        BCL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1) (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 mi hmi Ki hKi hmiz q y r ti
        hSegment).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.1))
          ((q,(y,r)),(ti,tk)) hPi
  have hGk : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      secondTaylorRemainder (fun s : ℝ =>
        BCL (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) (z.1.1,(z.1.2.1,s))) z.1.2.2)
      ((q,(y,r)),(ti,tk)) :=
    (contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 mk hmk Kk hKk hmkz q y r tk
        hSegment).comp (f := fun z : (ℝ × (R3 × ℝ)) × (T × T) => (z.1,z.2.2))
          ((q,(y,r)),(ti,tk)) hPk
  -- (j) GN_i = -(realHalfOperatorAdjointL G_i): fixed CLM after (e); MINUS kept
  have hGNi : ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      -(realHalfOperatorAdjointL (secondTaylorRemainder (fun s : ℝ =>
        BCL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1) (z.1.1,(z.1.2.1,s)))
          z.1.2.2)))
      ((q,(y,r)),(ti,tk)) :=
    ((ContinuousLinearMap.contDiff realHalfOperatorAdjointL).comp_contDiffAt
      ((q,(y,r)),(ti,tk)) hGi).neg
  unfold referenceAdjacentGainedCommutatorLow
  exact ((hNi.clm_comp (hKL.clm_comp hLk)).neg.add
      (hNi.clm_comp (hTl.clm_comp hGk))).sub
      (hGNi.clm_comp (hNk.clm_comp hSl))

/-! ### A4. ONE uniform radial box (chosen before the families) and uniform op-norm caps. -/

theorem exists_reference_commonRadius_adjacentGainedCommutator_smooth_caps
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (mi : T × R3 → ℝ) (hmi : ContDiff ℝ ∞ mi) (Ki : Set R3) (hKi : IsCompact Ki)
        (hmiz : ∀ t x, x ∉ Ki → mi (t,x) = 0)
        (mk : T × R3 → ℝ) (hmk : ContDiff ℝ ∞ mk) (Kk : Set R3) (hKk : IsCompact Kk)
        (hmkz : ∀ t x, x ∉ Kk → mk (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ∀ ti ∈ Kt, ∀ tk ∈ Kt,
            ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
              CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)
                z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) ∧
            ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
              CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)
                z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) ∧
            ‖CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz ti)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 p.2.1 p.2.2‖ ≤ M ∧
            ‖CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz ti)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 p.2.1 p.2.2‖ ≤ M := by
  obtain ⟨lam,Lam,d0,_,hd0,hd0ρ,hRoom0⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d0,hd0,hd0ρ,?_⟩
  intro mi hmi Ki hKi hmiz mk hmk Kk hKk hmkz Kt hKt
  have hSeg : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ θ ∈ Icc (0 : ℝ) 1,
      (p.1,(p.2.1,θ*p.2.2)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0) := by
    intro p hp θ hθ
    have hr : |p.2.2| ≤ d0 := abs_le.mpr hp.2.2
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hScaled : |θ*p.2.2| ≤ d0 := by
      rw [abs_mul]
      exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans_eq (one_mul _)).trans hr
    exact ⟨hp.1,hp.2.1,abs_le.mp hScaled⟩
  have hHighSm : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ ti tk : T,
      ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
        CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
          (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)
          z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) := fun p hp ti tk =>
    contDiffAt_referenceAdjacentGainedCommutatorHigh_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg
      mi hmi Ki hKi hmiz mk hmk Kk hKk hmkz p.1 p.2.1 p.2.2 ti tk
      (fun θ hθ => (hRoom0 (p.1,(p.2.1,θ*p.2.2)) (hSeg p hp θ hθ)).2.2.1)
      (fun θ hθ => (hRoom0 (p.1,(p.2.1,θ*p.2.2)) (hSeg p hp θ hθ)).2.2.2.1)
  have hLowSm : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ ti tk : T,
      ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
        CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
          (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2)
          z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) := fun p hp ti tk =>
    contDiffAt_referenceAdjacentGainedCommutatorLow_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
      mi hmi Ki hKi hmiz mk hmk Kk hKk hmkz p.1 p.2.1 p.2.2 ti tk
      (fun θ hθ => (hRoom0 (p.1,(p.2.1,θ*p.2.2)) (hSeg p hp θ hθ)).2.2.1)
  have hKp : IsCompact ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ (Kt ×ˢ Kt)) :=
    (isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)).prod (hKt.prod hKt)
  have hContH : ContinuousOn (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
        (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) z.1.1 z.1.2.1 z.1.2.2)
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ (Kt ×ˢ Kt)) :=
    fun z hz => (hHighSm z.1 hz.1 z.2.1 z.2.2).continuousAt.continuousWithinAt
  have hContL : ContinuousOn (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
      CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz z.2.1)
        (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz z.2.2) z.1.1 z.1.2.1 z.1.2.2)
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ (Kt ×ˢ Kt)) :=
    fun z hz => (hLowSm z.1 hz.1 z.2.1 z.2.2).continuousAt.continuousWithinAt
  obtain ⟨MH,hMH⟩ := hKp.exists_bound_of_continuousOn hContH
  obtain ⟨ML,hML⟩ := hKp.exists_bound_of_continuousOn hContL
  refine ⟨max (max MH ML) 0, le_max_right _ _, ?_⟩
  intro p hp ti hti tk htk
  have hz : (p,(ti,tk)) ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ (Kt ×ˢ Kt) :=
    ⟨hp,hti,htk⟩
  exact ⟨hHighSm p hp ti tk, hLowSm p hp ti tk,
    (hMH (p,(ti,tk)) hz).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hML (p,(ti,tk)) hz).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjacentGainedCommutatorHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjacentGainedCommutatorLow
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_referenceAdjacentGainedCommutator_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointHalfRadialSecondRemainder_joint_of_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjacentGainedCommutatorHigh_of_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjacentGainedCommutatorLow_of_segment
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjacentGainedCommutator_smooth_caps
