import Calderon.ActualQradFirstOutputGraphTransport
import Calderon.ActualQradSectionContinuityAndHighGraph
import Calderon.ActualFinitePairedRadialRemainderClosedSections
import Calderon.ActualPiNativeOperatorGerms
import Calderon.ActualQradReferenceProfileEnergy
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

include hg in
theorem exists_reference_commonRadius_finite_radial_coefficient_first_output_sections
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
    ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
      (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ i t x, x ∉ Km → m i (t,x)=0),
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
    ∀ (tt : R3 → T), ContDiff ℝ ∞ tt → ∀ (n : ℕ) (u : R3 → Hi),
    ContDiff ℝ ∞ u → HasCompactSupport u →
    (∀ y, sphereSobolevPartialSum (3/2 : ℝ) n (u y)=u y) →
    (∀ y ∈ tsupport u, ‖y-y0‖ ≤ ρ ∧ |R y| < d) →
    ∃ rS lS : Fin 3 → R3 → Hi,
      (∀ i, ContDiff ℝ ∞ (rS i)) ∧ (∀ i, Continuous (lS i)) ∧
      (∀ i y, y ∉ tsupport u → rS i y=0 ∧ lS i y=0) ∧
      ∀ i y,
        Ihi (rS i y) = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y))
          (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) (u y)) ∧
        Ihi (lS i y) = NML (smoothMultiplierLowerJets
          (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))) (Sh q y (R y) (u y)) := by
  have hSections := exists_reference_commonRadius_finitePairedRadialRemainder_closed_sections
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel
  rcases hSections with ⟨dG,δS,-,-,hδS,hδSρ,-,G,hSec⟩
  have hLowFull := exists_reference_commonRadius_highMultiplierRemainder_lowerIdentity
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hKernel
  rcases hLowFull with ⟨d0,hd0,hLow⟩
  let d := min δS d0
  have hd : 0 < d := lt_min hδS hd0
  refine ⟨d,hd,(min_le_left _ _).trans hδSρ,?_⟩
  intro m hm Km hKm hmz q hq R hRsm tt httsm n u hUsm hUc hcut hRoom
  let rS : Fin 3 → R3 → Hi := fun i y =>
    referenceFiniteGaugeAdjointSecondRemainder g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n
      (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) q y (R y) (u y)
  let pS : Fin 3 → R3 → Hi := fun i y =>
    referenceFiniteHarmonicProductHighSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n
      (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) q y (R y) (u y)
  let lS : Fin 3 → R3 → Hi := fun i y =>
    pS i y - GHr (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) q y (R y) (u y)
  have hSecData : ∀ i : Fin 3,
      ContDiff ℝ ∞ (pS i) ∧ ContDiff ℝ ∞ (rS i) ∧ ∀ y,
      Ihi (pS i y) = (secondTaylorRemainder (fun s : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) (R y))
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))
          (sphereSobolevPartialSum (3/2 : ℝ) n (u y))) ∧
      Ihi (rS i y) = (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) (R y))
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))
          (sphereSobolevPartialSum (3/2 : ℝ) n (u y))) := by
    intro i
    have hmbar : ContDiff ℝ ∞ (fun z : R3 × R3 => m i (tt z.1,z.2)) :=
      (hm i).comp ((httsm.comp contDiff_fst).prodMk contDiff_snd)
    have hzbar : ∀ y x, x ∉ Km → (fun z : R3 × R3 => m i (tt z.1,z.2)) (y,x)=0 :=
      fun y x hx => hmz i (tt y) x hx
    have hQbar : ∀ y, coefficientValue 3
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) =
        fun x => (fun z : R3 × R3 => m i (tt z.1,z.2)) (y,x) := by
      intro y
      funext x
      exact coefficientValue_commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y) x
    have hRoomS : ∀ y ∈ tsupport u, ‖y-y0‖ ≤ ρ ∧ |R y| < δS :=
      fun y hy => ⟨(hRoom y hy).1,((hRoom y hy).2).trans_le (min_le_left _ _)⟩
    have hS := hSec n q hq R hRsm (fun z : R3 × R3 => m i (tt z.1,z.2)) hmbar Km hKm hzbar
      (fun y => commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) hQbar u hUsm hUc hRoomS
    rcases hS with ⟨hP,hA,-,-,-,-,hGraph⟩
    exact ⟨hP,hA,hGraph⟩
  have hU0 : ∀ y, y ∉ tsupport u → u y=0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hZero : ∀ i y, y ∉ tsupport u → rS i y=0 ∧ lS i y=0 := by
    intro i y hy
    constructor
    · simp only [rS,hU0 y hy,map_zero]
    · simp only [lS,pS,hU0 y hy,map_zero,sub_zero]
  have hGHc : ∀ i y, y ∈ tsupport u → ContinuousAt (fun x : R3 =>
      GHr (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)) q x (R x)) y := by
    intro i y hy
    have hHigh := (hLow q hq y (hRoom y hy).1 (R y)
      (((hRoom y hy).2).trans_le (min_le_right _ _))).1
    have hZsm : ContDiff ℝ ∞ (fun x : R3 => (((q,(x,R x)) : Pphys),tt x)) :=
      (contDiff_const.prodMk (contDiff_id.prodMk hRsm)).prodMk httsm
    exact ((contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
      g L y0 Φ B ε C ρ H a w hData (m i) (hm i) Km hKm (hmz i) hcalc hF hO hD τ0 q y (R y) (tt y)
        hHigh).comp (f := fun x : R3 => (((q,(x,R x)) : Pphys),tt x)) y hZsm.contDiffAt).continuousAt
  have hlC : ∀ i, Continuous (lS i) := by
    intro i
    have hGu := continuous_clm_apply_of_closed_vanishing (tsupport u) (isClosed_tsupport _)
      (fun x : R3 => GHr (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt x)) q x (R x))
      u hUsm.continuous (fun y hy => hGHc i y hy) hU0
    exact ((hSecData i).1.continuous).sub hGu
  refine ⟨rS,lS,fun i => (hSecData i).2.1,hlC,hZero,?_⟩
  intro i y
  by_cases hy : y ∈ tsupport u
  · have hG := (hLow q hq y (hRoom y hy).1 (R y)
        (((hRoom y hy).2).trans_le (min_le_right _ _))).2
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y)) (u y)
    have h := referenceNative_finite_first_output_graph_transport
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      n (u y) (hcut y) (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) (tt y))
      q y (R y) (pS i y) (rS i y) ((hSecData i).2.2 y).1 ((hSecData i).2.2 y).2 hG
    exact h
  · simp only [(hZero i y hy).1,(hZero i y hy).2,hU0 y hy,map_zero,and_self]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
