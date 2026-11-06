import Calderon.ActualAdjacentGainedCommutatorCaps
import Calderon.NativeHalfCoefficientCommutation
import Calderon.AdjacentGainedBracketAlgebra
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

local instance actualBracketThreeHalfComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualBracketHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualBracketNegativeHalfComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualBracketHighHighComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance actualBracketHighHalfComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance actualBracketHalfHalfComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance actualBracketHalfNegComplete :
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

local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

theorem exists_reference_commonRadius_referenceAdjacentGainedCommutatorLow_bracket
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
        (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ t x, x ∉ Km → m (t,x) = 0) (t : T) (Qk : SmoothCoefficientJets 3),
        ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : SphereSobolev (3/2 : ℝ),
          CL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) Qk q y r (Ihi u) =
            NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))
              (Sl q y r ((secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r) (NMH Qk u))) -
            (secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r)
              (NML (smoothMultiplierLowerJets Qk)
                (NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))
                  (Sh q y r u))) := by
  have physicalRoom := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases physicalRoom with ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩
  have lowGraphRoom := exists_reference_commonRadius_radialAdjointSharpSecondCommutator_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases lowGraphRoom with ⟨dL,hdL,hdLρ,hKL⟩
  refine ⟨min dL (d0/2), lt_min hdL (half_pos hd0), (min_le_left _ _).trans hdLρ, ?_⟩
  intro T _ _ _ m hm Km hKm hmz t Qk q hq y hy r hr u
  have hrL : |r| ≤ dL := hr.trans (min_le_left _ _)
  have hr2 : |r| ≤ d0/2 := hr.trans (min_le_right _ _)
  have hr0 : |r| < d0 := hr2.trans_lt (by linarith)
  have hyBall : y ∈ closedBall y0 ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| ≤ d0 := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)).trans hr0.le
  have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun θ hθ => (hRoom0 (q,(y,θ*r)) ⟨hq,hyBall,abs_le.mp (hScaled θ hθ)⟩).2.2.1
  let Qi := commonSupportCoefficientFamily 3 m hm Km hKm hmz t
  let Th := secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r
  let Tl := secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r
  let Gi := secondTaylorRemainder (fun s : ℝ => BCL Qi (q,(y,s))) r
  let Gk := secondTaylorRemainder (fun s : ℝ => BCL Qk (q,(y,s))) r
  have hK : ∀ v : SphereSobolev (3/2 : ℝ),
      KbL q y r (Ihi v) = Tl (Sh q y r v) - Sl q y r (Th v) := hKL q hq y hy r hrL
  have hG : ∀ v : SphereSobolev (3/2 : ℝ),
      Gk (Ihi v) = Sh q y r (NMH Qk v) - NML (smoothMultiplierLowerJets Qk) (Sh q y r v) :=
    referenceSmoothMultiplierSecondRemainder_upper_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Qk q y r hSegment
  have hSl : ∀ v : SphereSobolev (3/2 : ℝ), Sl q y r (Ihi v) = Jlo (Sh q y r v) := fun v =>
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hML : ∀ z : SphereSobolev (1/2 : ℝ),
      Jlo (NML (smoothMultiplierLowerJets Qk) z) = NMN (smoothMultiplierLowerJets Qk) (Jlo z) := fun z =>
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A z)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Qk))
  have hMH : ∀ v : SphereSobolev (3/2 : ℝ),
      Ihi (NMH Qk v) = NML (smoothMultiplierLowerJets Qk) (Ihi v) := fun v =>
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Qk
        (smoothMultiplierLowerJets Qk) (coefficientValue_smoothMultiplierLowerJets Qk).symm)
  have hNegativeFactor := referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0 hKernel q y r t hSegment
  have hNF := hNegativeFactor.1
  have hGn : ∀ z : SphereSobolev (1/2 : ℝ),
      (-(realHalfOperatorAdjointL Gi)) (Jlo z) =
        Tl (NML (smoothMultiplierLowerJets Qi) z) - NMN (smoothMultiplierLowerJets Qi) (Tl z) :=
    fun z => (ContinuousLinearMap.neg_apply _ _).trans (hNF z).symm
  have hComm : ∀ z : SphereSobolev (1/2 : ℝ),
      NML (smoothMultiplierLowerJets Qi) (NML (smoothMultiplierLowerJets Qk) z) =
        NML (smoothMultiplierLowerJets Qk) (NML (smoothMultiplierLowerJets Qi) z) :=
    nativeHalfCoefficientMulL_lowerJets_comm_apply hcalc hF hO hD τ0 Qi Qk
  have hAlg := adjacentGainedLow_eq_bracket_of_native_graphs (Sh q y r) Th (Gk.comp Ihi)
    (Sl q y r) Tl (KbL q y r) (-(realHalfOperatorAdjointL Gi))
    (NMH Qk) (NML (smoothMultiplierLowerJets Qi)) (NML (smoothMultiplierLowerJets Qk))
    (NMN (smoothMultiplierLowerJets Qi)) (NMN (smoothMultiplierLowerJets Qk))
    hK hG hGn hSl hML hMH hComm u
  simpa only [referenceAdjacentGainedCommutatorLow, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    Qi, Th, Tl, Gi, Gk] using hAlg
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
