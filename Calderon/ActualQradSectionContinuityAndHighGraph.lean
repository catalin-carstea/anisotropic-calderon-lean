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

lemma continuous_clm_apply_of_closed_vanishing
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set R3) (hS : IsClosed S) (Aop : R3 → E →L[ℝ] F) (v : R3 → E) (hv : Continuous v)
    (hA : ∀ y ∈ S, ContinuousAt Aop y) (hvS : ∀ y : R3, y ∉ S → v y = 0) :
    Continuous (fun y => Aop y (v y)) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ S
  · exact (hA y hy).clm_apply hv.continuousAt
  · have hN : Sᶜ ∈ 𝓝 y := hS.isOpen_compl.mem_nhds hy
    have hEq : (fun _ : R3 => (0 : F)) =ᶠ[𝓝 y] (fun x => Aop x (v x)) := by
      filter_upwards [hN] with x hx
      show (0 : F) = Aop x (v x)
      rw [hvS x ((Set.mem_compl_iff S x).mp hx), map_zero]
    exact continuousAt_const.congr hEq

/-! ### N0 (L2): exact high commutator identity and two-endpoint segment on one physical room.
Same producers and same proof as Root's `exists_reference_commonRadius_finite_radial_coefficient_first_output_lifts`. -/

theorem exists_reference_commonRadius_highMultiplierRemainder_lowerIdentity
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d0 : ℝ, 0 < d0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| < d0 →
        (∀ θ ∈ Icc (0 : ℝ) 1,
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,θ*r)).IsInvertible ∧
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,θ*r)).IsInvertible) ∧
        ∀ (Q : SmoothCoefficientJets 3) (v : Hi),
          Ihi (GHr Q q y r v) = Sh q y r (NMH Q v) - NML (smoothMultiplierLowerJets Q) (Sh q y r v) := by
  have physicalRoom := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases physicalRoom with ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩
  refine ⟨d0,hd0,?_⟩
  intro q hq y hy r hr0
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| ≤ d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)).trans hr0.le
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun θ hθ => (hRoom0 (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp (hScaled θ hθ)⟩).2.2.1
  have hTube : ∀ s : ℝ, |s| < d0 →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,s)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,s)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,s))).IsInvertible ∧
      (q,(y,s)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc := by
    intro s hs
    have hz := hRoom0 (q,(y,s)) ⟨hq,hyBall,abs_le.mp hs.le⟩
    refine ⟨hz.1,hz.2.1.1,
      isInvertible_referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,s)) lam hz.2.1,?_⟩
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hz.2.2.2.1
  refine ⟨fun θ hθ => ?_, fun Q v => ?_⟩
  · have hz := (hRoom0 (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp (hScaled θ hθ)⟩).2.2.2.1
    first
    | exact hz
    | (unfold referenceGaugeNormalHighInvertibleLocus at hz; exact hz)
  · have hLower := referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hKernel Q q y r d0 lam Lam
        hr0 hSegment hTube
    have hGH : Ihi (GHr Q q y r v) =
        (secondTaylorRemainder (fun s : ℝ => BCL Q (q,(y,s))) r) (Ihi v) := by
      simpa only [referenceHighSmoothMultiplierSecondRemainder,
        referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,ContinuousLinearMap.comp_apply] using
        (congrArg (fun A : Hi →L[ℝ] Half => A v) hLower)
    exact hGH.trans (referenceSmoothMultiplierSecondRemainder_upper_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q q y r hSegment v)

/-! ### N1–N6 Actual original-Pi Qrad self row: two separately integrable weighted squared norms. -/


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
