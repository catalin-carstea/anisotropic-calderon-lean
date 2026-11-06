import Calderon.ActualAdjacentGainedSameRoom

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

/-! ### A1. The named actual adjacent maps (literally the two sides of v004 H13). -/

local notation "CH" => referenceAdjacentGainedCommutatorHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "CL" => referenceAdjacentGainedCommutatorLow
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

attribute [local irreducible] referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

theorem exists_reference_commonRadius_adjacentGainedCommutator_finite_family_caps_and_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ i k : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ∀ ti ∈ Kt, ∀ tk ∈ Kt,
            ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
              CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2.1)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z.2.2)
                z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) ∧
            ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × (T × T) =>
              CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2.1)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) z.2.2)
                z.1.1 z.1.2.1 z.1.2.2) (p,(ti,tk)) ∧
            ‖CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) ti)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) tk) p.1 p.2.1 p.2.2‖ ≤ M ∧
            ‖CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) ti)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) tk) p.1 p.2.1 p.2.2‖ ≤ M ∧
            ∀ u : SphereSobolev (3/2 : ℝ),
              Jlo (CH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) ti)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) tk) p.1 p.2.1 p.2.2 u) =
              CL (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) ti)
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) tk) p.1 p.2.1 p.2.2 (Ihi u) := by
  have hFull := exists_reference_commonRadius_adjacentGainedCommutator_smooth_caps_and_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hFull with ⟨d,hd,hdρ,hA⟩
  refine ⟨d,hd,hdρ,?_⟩
  intro m hm Km hKm hmz Kt hKt
  have hPair (i k : Fin 3) := hA (m i) (hm i) Km hKm (hmz i)
    (m k) (hm k) Km hKm (hmz k) Kt hKt
  choose M hM hCaps using hPair
  let Bnd : ℝ := ∑ i : Fin 3, ∑ k : Fin 3, M i k
  have hBnd : 0 ≤ Bnd := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hM i k
  have hMle (i k : Fin 3) : M i k ≤ Bnd := by
    have hInner : M i k ≤ ∑ l : Fin 3, M i l :=
      Finset.single_le_sum (fun l _ => hM i l) (Finset.mem_univ k)
    have hOuter : (∑ l : Fin 3, M i l) ≤ Bnd :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun l _ => hM j l) (Finset.mem_univ i)
    exact hInner.trans hOuter
  refine ⟨Bnd,hBnd,?_⟩
  intro i k p hp ti hti tk htk
  have hc := hCaps i k p hp ti hti tk htk
  exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (hMle i k),hc.2.2.2.1.trans (hMle i k),hc.2.2.2.2⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
