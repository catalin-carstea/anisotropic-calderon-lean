import Calderon.ActualRadialCoefficientDiagonalCaps
import Calderon.QradSignedSelfRowContinuity
import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Physical Qrad signed self-row.
Uses the first-output lifts, CL bracket, radial coefficient pivots,
finite-family adjacent caps, and QradFourIndexNormIdentity/WeakForm. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL harmonicSphereSubspace
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialAdjointSharpSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutator
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
  referenceAdjacentGainedCommutatorHigh referenceAdjacentGainedCommutatorLow

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

attribute [local irreducible] commonSupportCoefficientFamily

theorem exists_reference_commonRadius_joint_radial_and_gained_coefficient_caps
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∃ M : ℝ, 0 ≤ M ∧
          (∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ∀ t ∈ Kt,
            ContDiffAt ℝ ∞ (fun z : Pphys × T =>
              (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
                (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))) (p,t) ∧
            ContDiffAt ℝ ∞ (fun z : Pphys × T =>
              (NML (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
                (Sh z.1.1 z.1.2.1 z.1.2.2)) (p,t) ∧
            ContDiffAt ℝ ∞ (fun z : Pphys × T =>
              (secondTaylorRemainder (fun s : ℝ => RAL (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
                (NML (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2)))) (p,t) ∧
            ContDiffAt ℝ ∞ (fun z : Pphys × T =>
              (NMN (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
                (Sl z.1.1 z.1.2.1 z.1.2.2)) (p,t) ∧
            ‖(secondTaylorRemainder (fun s : ℝ => RAH (p.1,(p.2.1,s))) p.2.2).comp
                (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))‖ ≤ M ∧
            ‖(NML (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))).comp
                (Sh p.1 p.2.1 p.2.2)‖ ≤ M ∧
            ‖(secondTaylorRemainder (fun s : ℝ => RAL (p.1,(p.2.1,s))) p.2.2).comp
                (NML (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)))‖ ≤ M ∧
            ‖(NMN (smoothMultiplierLowerJets
                (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))).comp
                (Sl p.1 p.2.1 p.2.2)‖ ≤ M) ∧
          (∀ i k : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ∀ ti ∈ Kt, ∀ tk ∈ Kt,
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
                (commonSupportCoefficientFamily 3 (m k) (hm k) Km hKm (hmz k) tk) p.1 p.2.1 p.2.2 (Ihi u)) := by
  have hDfull := exists_reference_commonRadius_radialCoefficient_diagonal_caps
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg T
  rcases hDfull with ⟨dD,hdD,hdDρ,hDcap⟩
  have hFfull := exists_reference_commonRadius_adjacentGainedCommutator_finite_family_caps_and_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel T
  rcases hFfull with ⟨dF,hdF,_,hFcap⟩
  refine ⟨min dD dF,lt_min hdD hdF,(min_le_left _ _).trans hdDρ,?_⟩
  intro m hm Km hKm hmz Kt hKt
  have hDSel := hDcap m hm Km hKm hmz Kt hKt
  rcases hDSel with ⟨MD,hMD,hDall⟩
  have hFSel := hFcap m hm Km hKm hmz Kt hKt
  rcases hFSel with ⟨MF,hMF,hFall⟩
  refine ⟨max MD MF,hMD.trans (le_max_left _ _),?_,?_⟩
  · intro i p hp t ht
    have hpD : p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dD) dD) :=
      ⟨hp.1,hp.2.1,(neg_le_neg (min_le_left dD dF)).trans hp.2.2.1,
        hp.2.2.2.trans (min_le_left dD dF)⟩
    have hc := hDall i p hpD t ht
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,
      hc.2.2.2.2.1.trans (le_max_left _ _),
      hc.2.2.2.2.2.1.trans (le_max_left _ _),
      hc.2.2.2.2.2.2.1.trans (le_max_left _ _),
      hc.2.2.2.2.2.2.2.trans (le_max_left _ _)⟩
  · intro i k p hp ti hti tk htk
    have hpF : p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dF) dF) :=
      ⟨hp.1,hp.2.1,(neg_le_neg (min_le_right dD dF)).trans hp.2.2.1,
        hp.2.2.2.trans (min_le_right dD dF)⟩
    have hc := hFall i k p hpF ti hti tk htk
    exact ⟨hc.1,hc.2.1,hc.2.2.1.trans (le_max_right _ _),
      hc.2.2.2.1.trans (le_max_right _ _),hc.2.2.2.2⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
