import Calderon.ActualHighRadialCommutatorGainCore
import Calderon.ActualReferenceRadialAdjointSharpSecondCommutatorCoercivity
import Calderon.ActualReferenceSharpRotationRemainderDefinition
import Calderon.ActualHighSmoothMultiplierBoundaryCommutator
import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderCoercivity
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderTopologyCoercivity
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.ActualReferenceUpperRotationCommutatorJointJets
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.ActualReferencePairedHighRadialRemainderLocalSmoothness
import Calderon.ActualReferenceGaugeNormalHalfRemainder
import Calderon.ActualReferenceGaugeTangentReciprocalSkew
import Calderon.ActualReferenceNormalizedHighDefectCompletion
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor
import Calderon.ActualAdjointHighSmoothMultiplierSignedTaylorGraphCoercivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceSharpRadialTraceFamily
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL
  referenceGaugeNormalHighInvertibleLocus
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceNormalizedAdjointHighDefectFamily referenceNormalizedAdjointHalfDefectFamily
  referenceRadialSkewProductJets referenceRadialSkewDerivativeJets
  referenceRadialTangentSecondCommutator referenceRadialDefectSecondCommutator
  referenceRadialAdjointSharpSecondCommutator referenceSharpRadialRotationSecondRemainder
  referenceLowerRadialRotationSecondRemainder referenceSharpRadialRotationCommutatorL
  referenceLowerRadialRotationCommutatorL sphereSobolevRotationL harmonicSphereSubspace
open SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion
attribute [local irreducible] referenceRadialTangentSecondCommutatorHigh
  referenceRadialDefectSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutatorHigh
  referenceHighSmoothMultiplierSecondRemainder
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder


attribute [local instance] highRadialGainThreeHalfComplete highRadialGainHalfComplete highRadialGainNegativeHalfComplete highRadialGainHighEndComplete highRadialGainHighHalfComplete highRadialGainHalfEndComplete highRadialGainHalfNegativeComplete
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
local notation "CJ" => referenceRadialSkewProductJets g L y0 Φ B ε C ρ H a w hData hg Room
local notation "DJ" => referenceRadialSkewDerivativeJets g L y0 Φ B ε C ρ H a w hData hg Room
local notation "Dl" => referenceNormalizedAdjointHalfDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Dh" => referenceNormalizedAdjointHighDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/- v004 (H0): the high frozen-coefficient remainder is the EXISTING owner
`referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder` (literally
`secondTaylorRemainder (fun t => referenceHighSmoothMultiplierBoundaryCommutatorFamily … Q (q,(y,t))) r`);
the v003 duplicate definition is removed. -/
local notation "GHr" => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0


/-! ### H11. Joint C^∞ of the ACTUAL KbarHigh at a point with the two actual radial
segments (MATHEMATICS.md H11 (a)-(f)). No continuity/bound/lift/gain premise. -/

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

/-- (a) High twin of the lower private rotation lemma of the JointSmoothness owner
(re-proved locally; `ActualReferenceRotationSignedRemainderJets` is not imported). -/
lemma contDiffAt_referenceSharpRadialRotationSecondRemainder_joint_of_segment_high
    (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z.1 z.2.1 z.2.2) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun z =>
    referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j (z.1.1,(z.1.2,z.2))
  let U : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hU : IsOpen U := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFU : ContDiffOn ℝ ∞ F U := by
    intro z hz
    have hi := (show (z.1.1,(z.1.2,z.2)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 from hz)
    unfold referenceRadialEndpointInvertibleLocus at hi
    have hA := contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (z.1.1,(z.1.2,z.2)) hi.1 hi.2.1
    exact (hA.comp (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z (contDiffAt_fst.fst.prodMk
      (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ((q,y),r) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F U hU hFU (q,y) r hSegment
  have hOut := hR.comp
    (f := fun z : ℝ × (R3 × ℝ) => ((z.1,z.2.1),z.2.2)) (q,(y,r))
      ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  simpa only [referenceSharpRadialRotationSecondRemainder,Function.comp_def,F] using hOut

/-- (c) Frozen common-support coefficient on the diagonal, through the EXISTING high
owner `contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment`. -/
lemma contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_diagonal
    (m : (ℝ × (R3 × ℝ)) × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x) = 0)
    (q : ℝ) (y : R3) (r : ℝ)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      GHr (commonSupportCoefficientFamily 3 m hm Km hKm hmz z) z.1 z.2.1 z.2.2) (q,(y,r)) := by
  have hJoint := contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0 q y r (q,(y,r)) hHigh
  simpa only [Function.comp_def] using
    hJoint.comp (f := fun z : ℝ × (R3 × ℝ) => (z,z)) (q,(y,r))
      (contDiffAt_id.prodMk contDiffAt_id)

/-- Tangent part of KbarHigh: (a), (b), (c). -/
lemma contDiffAt_referenceRadialTangentSecondCommutatorHigh_of_segment
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => referenceRadialTangentSecondCommutatorHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room z.1 z.2.1 z.2.2) (q,(y,r)) := by
  have hRot (i j : Fin 3) : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      referenceSharpRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i z.1 z.2.1 z.2.2) (q,(y,r)) :=
    contDiffAt_referenceSharpRadialRotationSecondRemainder_joint_of_segment_high
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r hSegment
  have hCoef (i j : Fin 3) : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j z)) (q,(y,r)) := by
    simpa only [referenceRadialSkewProductJets] using
      (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (referenceRadialSkewProductCoefficient g L y0 Φ ρ a Room i j)
      (contDiff_referenceRadialSkewProductCoefficient g L y0 Φ B ε C ρ H a w hData hg Room i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceRadialSkewProductCoefficient_support
        g L y0 Φ B ε C ρ H a w hData Room i j)).contDiffAt
  have hCJ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      GHr (CJ 3 i j z) z.1 z.2.1 z.2.2) (q,(y,r)) := by
    simpa only [referenceRadialSkewProductJets] using
      contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_diagonal
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (referenceRadialSkewProductCoefficient g L y0 Φ ρ a Room i j)
      (contDiff_referenceRadialSkewProductCoefficient g L y0 Φ B ε C ρ H a w hData hg Room i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceRadialSkewProductCoefficient_support g L y0 Φ B ε C ρ H a w hData Room i j)
      q y r hHigh
  have hDJ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      GHr (DJ 3 i j z) z.1 z.2.1 z.2.2) (q,(y,r)) := by
    simpa only [referenceRadialSkewDerivativeJets] using
      contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_diagonal
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (referenceRadialSkewDerivativeCoefficient g L y0 Φ ρ a Room i j)
      (contDiff_referenceRadialSkewDerivativeCoefficient
        g L y0 Φ B ε C ρ H a w hData hg Room i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceRadialSkewDerivativeCoefficient_support
        g L y0 Φ B ε C ρ H a w hData hg Room i j)
      q y r hHigh
  unfold referenceRadialTangentSecondCommutatorHigh
  simp only [referenceHighSmoothMultiplierSecondRemainder,
    referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder] at hCJ hDJ ⊢
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (((hRot i j).clm_comp (hCoef i j)).sub
    (contDiffAt_const.clm_comp (hCJ i j))).sub
      (contDiffAt_const.clm_comp (hDJ i j))

/-- Defect part of KbarHigh: (d), (e), (f). -/
lemma contDiffAt_referenceRadialDefectSecondCommutatorHigh_of_segment
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => referenceRadialDefectSecondCommutatorHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room z.1 z.2.1 z.2.2) (q,(y,r)) := by
  have hSh : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => Sh z.1 z.2.1 z.2.2) (q,(y,r)) :=
    (contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment).1
  have hDl : ContDiffAt ℝ ∞ Dl (q,(y,r)) := by
    unfold referenceNormalizedAdjointHalfDefectFamily
    exact (contDiffAt_referenceGaugeNormalHalfSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r hSegment).add
      (contDiff_referenceGaugeTangentReciprocalResidualHalfFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room).contDiffAt
  have hHighLoc : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc := by
    intro θ hθ
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hHigh θ hθ
  have hDh : ContDiffAt ℝ ∞ Dh (q,(y,r)) := by
    unfold referenceNormalizedAdjointHighDefectFamily
    exact (contDiffAt_referenceNormalizedAdjointHighNormalSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q y r hHighLoc).add
      (contDiff_referenceGaugeTangentReciprocalResidualThreeHalfFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room).contDiffAt
  unfold referenceRadialDefectSecondCommutatorHigh
  exact (hDl.clm_comp hSh).sub (hSh.clm_comp hDh)

/-- H11: joint C^∞ of the actual high gained commutator. -/
theorem contDiffAt_referenceRadialAdjointSharpSecondCommutatorHigh_of_segment
    (hreg : FixedDirichletRegularity) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hHigh : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => KbH z.1 z.2.1 z.2.2) (q,(y,r)) := by
  have hTan := contDiffAt_referenceRadialTangentSecondCommutatorHigh_of_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r hSegment hHigh
  have hDef := contDiffAt_referenceRadialDefectSecondCommutatorHigh_of_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg q y r hSegment hHigh
  unfold referenceRadialAdjointSharpSecondCommutatorHigh
  exact hTan.add hDef


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
