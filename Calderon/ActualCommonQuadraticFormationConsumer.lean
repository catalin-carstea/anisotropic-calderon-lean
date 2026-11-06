import Calderon.ActualCommonFirstWordQuadraticAdjoint

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCommonQuadraticFormationConsumer
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RevRoom" => ActualReverseEHigherLift.ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)


local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
def actualJacobianGuard (z : Pphys) : Prop :=
  ∀ ξ : UnitSphere, (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible
local notation "Jac" => actualJacobianGuard g L Φ

/-- Restrict all actual forward/reverse data without changing the retained packet. -/
theorem commonFirstWordRoom_mono (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    {d δ : ℝ} (M : CRoom hreg δ0 W d) (hδ : 0 < δ) (hle : δ ≤ d) : CRoom hreg δ0 W δ := by
  have hs := commonRoom_mono y0 ρ hle
  exact {
    rev := ActualCommonFirstWordQuadraticAdjoint.reverseERoom_mono g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W M.rev hδ hle
    germHigh := fun i t ht => M.germHigh i t ⟨hs ht.1,ht.2⟩
    germLow := fun i t ht => M.germLow i t ⟨hs ht.1,ht.2⟩
    compat := fun i t ht u => M.compat i t ⟨hs ht.1,ht.2⟩ u
    genGraph := fun V j t ht u => M.genGraph V j t ⟨hs ht.1,ht.2⟩ u
    genGerm := fun V j t ht => M.genGerm V j t ⟨hs ht.1,ht.2⟩
    pivot := fun i t ht u v => M.pivot i t ⟨hs ht.1,ht.2⟩ u v }

/-- The full formation's actual parent facts on exactly this common room. -/
theorem higherSParentFacts_of_common_room (hreg : FixedDirichletRegularity) (δ0 : ℝ)
    (W : CoeffRoom δ0) (δ : ℝ) (M : CRoom hreg δ0 W δ) :
    ActualHigherSFormation.HigherSParentFacts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 hreg δ0 W δ :=
  ⟨M.germHigh,M.compat,fun j t ht u => M.genGraph (Sum.inr ()) j t ht u,
    fun j t ht => M.genGerm (Sum.inr ()) j t ht⟩

/-- Add the actual geometric Jacobian guard by intersection, before every profile. -/
theorem exists_retained_common_formation_room (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, CRoom hreg δ0 W δ ∧ ∀ z ∈ commonRoom y0 ρ δ, Jac z := by
  obtain ⟨d,M⟩ := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  obtain ⟨lam,Lam,dG,hFin⟩ := exists_finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  have hδ : 0 < min d dG := lt_min M.rev.pos hFin.2.1
  have hs := commonRoom_mono y0 ρ (min_le_right d dG)
  exact ⟨min d dG,
    commonFirstWordRoom_mono g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W M hδ (min_le_left _ _),
    fun z hz => (hFin.2.2.2 z (hs hz)).2.2.2.2⟩

/-- Full formation with the same W and room as the quadratic adjoint. -/
theorem higherSOutputConclusions_of_common_room (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (M : CRoom hreg δ0 W δ)
    (hJac : ∀ z ∈ commonRoom y0 ρ δ, Jac z)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (δr Ar : ℝ) (p : ℕ) (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hMem : ∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ActualHigherSFormation.HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  have hFacts := higherSParentFacts_of_common_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ M
  have hRoom : ∀ x ∈ TS F0,
      ActualHigherSFormation.HigherSRoomAt hF hO hD g L y0 Φ B ε C ρ H a w hData hcalc τ0 δr Ar p q δ x :=
    fun x hx => ActualHigherSFormation.higherSRoomAt_of_mem_paramRoom hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
      δr Ar p hδr hAr q δ δ δ (le_refl _) (le_refl _) M.rev.room hJac x (hMem x hx)
  exact ActualHigherSFormation.higherSOutputConclusions_of_facts hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
    δr Ar p hδr hAr q hreg hq δ0 W δ hFacts g2 hg2 F0 hRoom

/-- One room before all metrics, profiles and test/input fields; every conclusion is derived. -/
theorem exists_retained_common_formation_and_quadratic_adjoint (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, CRoom hreg δ0 W δ ∧ (∀ z ∈ commonRoom y0 ρ δ, Jac z) ∧
      ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordLiftContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ActualCommonFirstWordQuadraticAdjoint.CommonQuadraticAdjointContract g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ g2 ∧
        ∀ δr Ar : ℝ, ∀ p : ℕ, ∀ hδr : 0 < δr, ∀ hAr : 0 < Ar, ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
          ∀ F0 : smoothCompactFiniteSphereCore hO hD,
            (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
            ActualHigherSFormation.HigherSOutputConclusions hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
              δr Ar p hδr hAr q hreg δ0 W g2 F0 := by
  obtain ⟨δ,M,hJac⟩ := exists_retained_common_formation_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,M,hJac,?_,?_⟩
  · exact ActualCommonFirstWordQuadraticAdjoint.commonFirstWordLiftContract_of_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ M
  · intro g2 hg2
    refine ⟨?_,?_⟩
    · exact ActualCommonFirstWordQuadraticAdjoint.commonQuadraticAdjointContract_of_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ M g2 hg2
    · intro δr Ar p hδr hAr q hq F0 hMem
      exact higherSOutputConclusions_of_common_room g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ M hJac g2 hg2 δr Ar p hδr hAr q hq F0 hMem

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCommonQuadraticFormationConsumer
