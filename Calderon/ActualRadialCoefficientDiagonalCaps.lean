import Calderon.QradSignedSelfRowContinuity
import Calderon.QradFourIndexNormIdentity
import Calderon.ActualAdjacentGainedBracket
import Calderon.ActualRadialCoefficientPivots
import Calderon.ActualQradFiniteFirstOutputLifts
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual physical Qrad signed self-row. Uses the first-output lifts, CL bracket, radial
coefficient pivots, finite-family adjacent caps, and QradFourIndexNormIdentity/WeakForm. -/
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

/-! ### §2 Diagonal uniform caps for RH, LH, RL, LL (coefficients frozen, uniform in t ∈ Kt). -/

theorem exists_reference_commonRadius_radialCoefficient_diagonal_caps
    (hreg : FixedDirichletRegularity)
    (T : Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ (m : Fin 3 → T × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0) (Kt : Set T), IsCompact Kt →
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ∀ t ∈ Kt,
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
                (Sl p.1 p.2.1 p.2.2)‖ ≤ M := by
  have hRootSelected1 := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hRootSelected1 with ⟨lam,Lam,d0,_,hd0,hd0ρ,hRoom0⟩
  refine ⟨d0,hd0,hd0ρ,?_⟩
  intro m hm Km hKm hmz Kt hKt
  have hSeg : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ θ ∈ Icc (0 : ℝ) 1,
      (p.1,(p.2.1,θ*p.2.2)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0) := by
    intro p hp θ hθ
    have hr : |p.2.2| ≤ d0 := abs_le.mpr hp.2.2
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hScaled : |θ*p.2.2| ≤ d0 := by
      rw [abs_mul]
      exact ((mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans_eq (one_mul _)).trans hr
    exact ⟨hp.1,hp.2.1,abs_le.mp hScaled⟩
  have hSegment : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0),
      ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    fun p hp θ hθ => (hRoom0 (p.1,(p.2.1,θ*p.2.2)) (hSeg p hp θ hθ)).2.2.1
  -- native multipliers, coefficient parameter t only (frozen in every Taylor integral)
  have hMH (i : Fin 3) : ContDiff ℝ ∞ (fun t : T =>
      NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t)) :=
    contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (m i) (hm i) Km hKm (hmz i)
  have hML (i : Fin 3) : ContDiff ℝ ∞ (fun t : T =>
      NML (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 (m i) (hm i) Km hKm (hmz i)
  have hMN (i : Fin 3) : ContDiff ℝ ∞ (fun t : T =>
      NMN (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) t))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeNegativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 (m i) (hm i) Km hKm (hmz i)
  -- actual radial remainders, jointly smooth in the physical point on the room
  have hTh : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2) (p,t) :=
    fun p hp t => (contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2
        (hSegment p hp)).2.comp (f := fun z : Pphys × T => z.1) (p,t) contDiffAt_fst
  have hSh : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T => Sh z.1.1 z.1.2.1 z.1.2.2) (p,t) :=
    fun p hp t => (contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2
        (hSegment p hp)).1.comp (f := fun z : Pphys × T => z.1) (p,t) contDiffAt_fst
  have hTl : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        secondTaylorRemainder (fun s : ℝ => RAL (z.1.1,(z.1.2.1,s))) z.1.2.2) (p,t) :=
    fun p hp t => (contDiffAt_referenceAdjointHalfRadialSecondRemainder_joint_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2.1 p.2.2
        (hSegment p hp)).comp (f := fun z : Pphys × T => z.1) (p,t) contDiffAt_fst
  have hSl : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T => Sl z.1.1 z.1.2.1 z.1.2.2) (p,t) :=
    fun p hp t => (contDiffAt_referenceLowerRadialTraceSecondRemainder_joint_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (hSegment p hp)).comp (f := fun z : Pphys × T => z.1) (p,t) contDiffAt_fst
  -- the four actual composites
  have cRH : ∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
          (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))) (p,t) :=
    fun i p hp t => (hTh p hp t).clm_comp ((hMH i).comp_contDiffAt (p,t) contDiffAt_snd)
  have cLH : ∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        (NML (smoothMultiplierLowerJets
          (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
          (Sh z.1.1 z.1.2.1 z.1.2.2)) (p,t) :=
    fun i p hp t => ((hML i).comp_contDiffAt (p,t) contDiffAt_snd).clm_comp (hSh p hp t)
  have cRL : ∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        (secondTaylorRemainder (fun s : ℝ => RAL (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
          (NML (smoothMultiplierLowerJets
            (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2)))) (p,t) :=
    fun i p hp t => (hTl p hp t).clm_comp ((hML i).comp_contDiffAt (p,t) contDiffAt_snd)
  have cLL : ∀ i : Fin 3, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0), ∀ t : T,
      ContDiffAt ℝ ∞ (fun z : Pphys × T =>
        (NMN (smoothMultiplierLowerJets
          (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
          (Sl z.1.1 z.1.2.1 z.1.2.2)) (p,t) :=
    fun i p hp t => ((hMN i).comp_contDiffAt (p,t) contDiffAt_snd).clm_comp (hSl p hp t)
  have hKp : IsCompact ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ Kt) :=
    (isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)).prod hKt
  have hRootSelected2 := exists_uniform_bound_fin3 _ hKp
    (fun i (z : Pphys × T) =>
      (secondTaylorRemainder (fun s : ℝ => RAH (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
        (NMH (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2)))
    (fun i z hz => (cRH i z.1 hz.1 z.2).continuousAt.continuousWithinAt)
  rcases hRootSelected2 with ⟨M1,hM1,hB1⟩
  have hRootSelected3 := exists_uniform_bound_fin3 _ hKp
    (fun i (z : Pphys × T) =>
      (NML (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
        (Sh z.1.1 z.1.2.1 z.1.2.2))
    (fun i z hz => (cLH i z.1 hz.1 z.2).continuousAt.continuousWithinAt)
  rcases hRootSelected3 with ⟨M2,hM2,hB2⟩
  have hRootSelected4 := exists_uniform_bound_fin3 _ hKp
    (fun i (z : Pphys × T) =>
      (secondTaylorRemainder (fun s : ℝ => RAL (z.1.1,(z.1.2.1,s))) z.1.2.2).comp
        (NML (smoothMultiplierLowerJets
          (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))))
    (fun i z hz => (cRL i z.1 hz.1 z.2).continuousAt.continuousWithinAt)
  rcases hRootSelected4 with ⟨M3,hM3,hB3⟩
  have hRootSelected5 := exists_uniform_bound_fin3 _ hKp
    (fun i (z : Pphys × T) =>
      (NMN (smoothMultiplierLowerJets
        (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z.2))).comp
        (Sl z.1.1 z.1.2.1 z.1.2.2))
    (fun i z hz => (cLL i z.1 hz.1 z.2).continuousAt.continuousWithinAt)
  rcases hRootSelected5 with ⟨M4,hM4,hB4⟩
  refine ⟨M1+M2+M3+M4, by linarith, ?_⟩
  intro i p hp t ht
  have hz : (p,t) ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d0) d0)) ×ˢ Kt := ⟨hp,ht⟩
  have h1 := hB1 i (p,t) hz
  have h2 := hB2 i (p,t) hz
  have h3 := hB3 i (p,t) hz
  have h4 := hB4 i (p,t) hz
  exact ⟨cRH i p hp t, cLH i p hp t, cRL i p hp t, cLL i p hp t,
    h1.trans (by linarith), h2.trans (by linarith), h3.trans (by linarith),
    h4.trans (by linarith)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
