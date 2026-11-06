import Calderon.ActualHighRadialKbarSmoothness
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


/-! ### H13. H8 instantiated: genuine common-support P_i, arbitrary P_k, one radius.
Every displayed graph hypothesis is discharged by a supplied source (MATHEMATICS.md H13);
(hN) keeps the source's MINUS sign: Gn_i = -(realHalfOperatorAdjointL G_i). -/

theorem exists_reference_commonRadius_adjacentGainedCommutator_high_graph_uniform
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
    (hmz : ∀ t x, x ∉ Km → m (t,x) = 0) (t : T) (Qk : SmoothCoefficientJets 3),
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : SphereSobolev (3/2 : ℝ),
          Jlo ((-((KbH q y r).comp
                ((NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)).comp (NMH Qk))) -
              (Sh q y r).comp ((secondTaylorRemainder (fun s : ℝ =>
                BCA (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r).comp
                  (NMH Qk)) -
              (secondTaylorRemainder (fun s : ℝ =>
                BCL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r).comp
                ((secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp (NMH Qk)) +
              (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp
                ((GHr (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) q y r).comp (NMH Qk)) +
              (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp
                ((NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)).comp
                  (GHr Qk q y r))) u) =
            (-((NMN (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))).comp
                ((KbL q y r).comp (NML (smoothMultiplierLowerJets Qk)))) +
              (NMN (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))).comp
                ((secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r).comp
                  (secondTaylorRemainder (fun s : ℝ => BCL Qk (q,(y,s))) r)) -
              (-(realHalfOperatorAdjointL (secondTaylorRemainder (fun s : ℝ =>
                  BCL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r))).comp
                ((NMN (smoothMultiplierLowerJets Qk)).comp (Sl q y r))) (Ihi u) := by
  have physicalRoom := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases physicalRoom with ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩
  have highGraphRoom := exists_reference_commonRadius_radialAdjointSharpSecondCommutatorHigh_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases highGraphRoom with ⟨dG,hdG,hdGρ,hKH⟩
  have lowGraphRoom := exists_reference_commonRadius_radialAdjointSharpSecondCommutator_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases lowGraphRoom with ⟨dL,hdL,_,hKL⟩
  have adjointGraphRoom := exists_reference_commonRadius_adjointHighSmoothMultiplierSecondRemainder_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel hg
  rcases adjointGraphRoom with ⟨dA,hdA,_,hAdj⟩
  refine ⟨min (min dG dL) (min dA (d0/2)),
    lt_min (lt_min hdG hdL) (lt_min hdA (half_pos hd0)),
    (min_le_left _ _).trans ((min_le_left _ _).trans hdGρ), ?_⟩
  intro T _ _ _ m hm Km hKm hmz t Qk
  intro q hq y hy r hr u
  have hrG : |r| ≤ dG := hr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrL : |r| ≤ dL := hr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrA : |r| ≤ dA := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : |r| ≤ d0/2 := hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr0 : |r| < d0 := hr2.trans_lt (by linarith)
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
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
  let Qi := commonSupportCoefficientFamily 3 m hm Km hKm hmz t
  let Th := secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r
  let Tl := secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r
  let Gi := secondTaylorRemainder (fun s : ℝ => BCL Qi (q,(y,s))) r
  let Gk := secondTaylorRemainder (fun s : ℝ => BCL Qk (q,(y,s))) r
  let GAi := secondTaylorRemainder (fun s : ℝ => BCA Qi (q,(y,s))) r
  -- (hKH), (hK)
  have hKH' : ∀ f : SphereSobolev (3/2 : ℝ), Jlo (KbH q y r f) = KbL q y r (Ihi f) :=
    hKH q hq y hy r hrG
  have hK : ∀ f : SphereSobolev (3/2 : ℝ),
      KbL q y r (Ihi f) = Tl (Sh q y r f) - Sl q y r (Th f) :=
    hKL q hq y hy r hrL
  -- (hS), (hT)
  have hS : ∀ f : SphereSobolev (3/2 : ℝ), Sl q y r (Ihi f) = Jlo (Sh q y r f) := fun f =>
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hT : ∀ f : SphereSobolev (3/2 : ℝ), Tl (Ihi f) = Jlo (Th f) := fun f =>
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A f)
      (referenceAdjointRadialSecondRemainder_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment)).symm
  -- (hMi), (hMk), (hMkN)
  have hIMap (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)) :
      Ihi (NMH Q f) = NML (smoothMultiplierLowerJets Q) (Ihi f) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJMap (Q : SmoothCoefficientJets 3) (v : SphereSobolev (1/2 : ℝ)) :
      Jlo (NML (smoothMultiplierLowerJets Q) v) = NMN (smoothMultiplierLowerJets Q) (Jlo v) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
        (smoothMultiplierLowerJets Q))
  -- (hA)
  have hA : ∀ f : SphereSobolev (3/2 : ℝ),
      Ihi (GAi f) = Th (NMH Qi f) - NML (smoothMultiplierLowerJets Qi) (Th f) :=
    fun f => hAdj q hq y hy r hrA Qi f
  -- (hGl)
  have hGl : ∀ v : SphereSobolev (1/2 : ℝ),
      Jlo (Gi v) = Sl q y r (NML (smoothMultiplierLowerJets Qi) v) -
        NMN (smoothMultiplierLowerJets Qi) (Sl q y r v) := fun v =>
    referenceSmoothMultiplierSecondRemainder_lower_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Qi q y r hSegment v
  -- (hGui), (hGuk): H6'
  have hGu (Q : SmoothCoefficientJets 3) : ∀ f : SphereSobolev (3/2 : ℝ),
      secondTaylorRemainder (fun s : ℝ => BCL Q (q,(y,s))) r (Ihi f) =
        Sh q y r (NMH Q f) - NML (smoothMultiplierLowerJets Q) (Sh q y r f) := fun f =>
    referenceSmoothMultiplierSecondRemainder_upper_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q q y r hSegment f
  -- (hGHi), (hGHk): H3 on the physical tube
  have hGH (Q : SmoothCoefficientJets 3) : ∀ f : SphereSobolev (3/2 : ℝ),
      Ihi (GHr Q q y r f) = secondTaylorRemainder (fun s : ℝ => BCL Q (q,(y,s))) r (Ihi f) :=
    fun f => by
      simpa only [referenceHighSmoothMultiplierSecondRemainder,
        referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder,
        ContinuousLinearMap.comp_apply] using
        (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A f)
          (referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hKernel Q q y r d0 lam Lam
            hr0 hSegment hTube))
  -- (hN): first conclusion of the supplied negative factor, MINUS kept
  have hNegativeFactor := referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0 hKernel q y r t hSegment
  have hNF := hNegativeFactor.1
  have hN : ∀ v : SphereSobolev (1/2 : ℝ),
      Tl (NML (smoothMultiplierLowerJets Qi) v) - NMN (smoothMultiplierLowerJets Qi) (Tl v) =
        (-(realHalfOperatorAdjointL Gi)) (Jlo v) :=
    fun v => (hNF v).trans (ContinuousLinearMap.neg_apply _ _).symm
  exact adjacentGainedCommutator_high_lower_graph Ihi Jlo (KbH q y r) Th (Sh q y r)
    (KbL q y r) Tl (Sl q y r) (NMH Qi) (NMH Qk) (GHr Qi q y r) (GHr Qk q y r) GAi
    (NML (smoothMultiplierLowerJets Qi)) (NML (smoothMultiplierLowerJets Qk)) Gi Gk
    (NMN (smoothMultiplierLowerJets Qi)) (NMN (smoothMultiplierLowerJets Qk))
    (-(realHalfOperatorAdjointL Gi))
    hKH' hK hS hT (hIMap Qi) (hIMap Qk) (hJMap Qk) hA hGl (hGu Qi) (hGu Qk) (hGH Qi) (hGH Qk)
    hN u


theorem exists_reference_commonRadius_adjacentGainedCommutator_high_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m) (Km : Set R3) (hKm : IsCompact Km)
    (hmz : ∀ t x, x ∉ Km → m (t,x) = 0) (t : T) (Qk : SmoothCoefficientJets 3) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : SphereSobolev (3/2 : ℝ),
          Jlo ((-((KbH q y r).comp
                ((NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)).comp (NMH Qk))) -
              (Sh q y r).comp ((secondTaylorRemainder (fun s : ℝ =>
                BCA (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r).comp
                  (NMH Qk)) -
              (secondTaylorRemainder (fun s : ℝ =>
                BCL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r).comp
                ((secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp (NMH Qk)) +
              (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp
                ((GHr (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) q y r).comp (NMH Qk)) +
              (secondTaylorRemainder (fun s : ℝ => RAH (q,(y,s))) r).comp
                ((NMH (commonSupportCoefficientFamily 3 m hm Km hKm hmz t)).comp
                  (GHr Qk q y r))) u) =
            (-((NMN (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))).comp
                ((KbL q y r).comp (NML (smoothMultiplierLowerJets Qk)))) +
              (NMN (smoothMultiplierLowerJets
                  (commonSupportCoefficientFamily 3 m hm Km hKm hmz t))).comp
                ((secondTaylorRemainder (fun s : ℝ => RAL (q,(y,s))) r).comp
                  (secondTaylorRemainder (fun s : ℝ => BCL Qk (q,(y,s))) r)) -
              (-(realHalfOperatorAdjointL (secondTaylorRemainder (fun s : ℝ =>
                  BCL (commonSupportCoefficientFamily 3 m hm Km hKm hmz t) (q,(y,s))) r))).comp
                ((NMN (smoothMultiplierLowerJets Qk)).comp (Sl q y r))) (Ihi u) := by
  have hFull := exists_reference_commonRadius_adjacentGainedCommutator_high_graph_uniform
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  rcases hFull with ⟨d,hd,hdρ,h⟩
  exact ⟨d,hd,hdρ,h m hm Km hKm hmz t Qk⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
