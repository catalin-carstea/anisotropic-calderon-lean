import Calderon.ActualAdjacentGainedCommutatorCaps

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

/-! ### A1. The named actual adjacent maps. -/

local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

attribute [local irreducible] referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

theorem exists_reference_commonRadius_adjacentGainedCommutator_smooth_caps_and_graph
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
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 p.2.1 p.2.2‖ ≤ M ∧
            ∀ u : SphereSobolev (3/2 : ℝ),
              Jlo (CH (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz ti)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 p.2.1 p.2.2 u) =
              CL (commonSupportCoefficientFamily 3 mi hmi Ki hKi hmiz ti)
                (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 p.2.1 p.2.2 (Ihi u) := by
  have hGraphFull := exists_reference_commonRadius_adjacentGainedCommutator_high_graph_uniform
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases hGraphFull with ⟨dG,hdG,hdGρ,hG⟩
  have hCapFull := exists_reference_commonRadius_adjacentGainedCommutator_smooth_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hCapFull with ⟨dA,hdA,hdAρ,hA⟩
  refine ⟨min dG dA,lt_min hdG hdA,(min_le_left _ _).trans hdGρ,?_⟩
  intro mi hmi Ki hKi hmiz mk hmk Kk hKk hmkz Kt hKt
  have hMFull := hA mi hmi Ki hKi hmiz mk hmk Kk hKk hmkz Kt hKt
  rcases hMFull with ⟨M,hM,hCaps⟩
  refine ⟨M,hM,?_⟩
  intro p hp ti hti tk htk
  have hpA : p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dA) dA) :=
    ⟨hp.1,hp.2.1,(neg_le_neg (min_le_right dG dA)).trans hp.2.2.1,
      hp.2.2.2.trans (min_le_right dG dA)⟩
  have hc := hCaps p hpA ti hti tk htk
  refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,?_⟩
  intro u
  have hy : ‖p.2.1-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
  have hr : |p.2.2| ≤ dG := (abs_le.mpr hp.2.2).trans (min_le_left dG dA)
  unfold referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow
  exact hG mi hmi Ki hKi hmiz ti
    (commonSupportCoefficientFamily 3 mk hmk Kk hKk hmkz tk) p.1 hp.1 p.2.1 hy p.2.2 hr u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
