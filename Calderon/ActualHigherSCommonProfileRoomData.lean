import Calderon.ActualHigherSOriginalDataCommonFirstWordRoom
import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.ActualHigherSQuarticBound
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSIntegratedPairing
import Calderon.FixedParameterProfilePullback
import Calderon.ActualHigherSZeroWordCoefficientBound
import Calderon.ActualHigherSQuadraticZeroQuarticRegularity
import Calderon.ActualHigherSQuadraticZeroQuarticRowBound
import Calderon.ActualHigherSPairingNormDiagnostic

/-! Complete original-data common room and uniform actual profile membership,
for ANY positive base room. Reusable by quartic dI and uniform graph dA without
a caller-supplied analytic callback. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ActualNormalizedSecondMetricDrift
  ReferenceDensityBounds ReferenceWeightedApproximation FixedParameterProfilePullback
  ActualScalarPrincipalAdjoint SpectralWeightedGraph SectionFiveErrorForms SmoothMetricFrame MovingFrameConnection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
  (hreg : FixedDirichletRegularity)
  (data : FullEPhysicalEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg)
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "GG" => fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  Room hreg data.Gcoord data.GN data.δ0 data.germs
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RD" => ActualCommonFirstWordQuadraticAdjoint.revDoubleHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L

local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "QR" => quarticWordRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Original-data common room and uniform membership into it and a base room. -/
structure CommonProfileRoomData (base : ℝ) where
  base_pos : 0 < base
  commonRadius : ℝ
  common : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs commonRadius
  guardRadius : ℝ
  guardRadius_eq_min : guardRadius = min base commonRadius
  guardRadius_pos : 0 < guardRadius
  guardRadius_le_base : guardRadius ≤ base
  guardRadius_le_common : guardRadius ≤ commonRadius
  epsG : ℝ
  epsG_pos : 0 < epsG
  epsG_le_one : epsG ≤ 1
  members : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ epsG →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      (∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom base) ∧
      (∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom commonRadius)

/-- Produce the complete room and membership output from original data for any base>0. -/
theorem exists_common_profile_room_data (hL : 0 < L)
    (hKernel : UnitBallValueTraceKernel τ0) (base : ℝ) (hbase : 0 < base) :
    Nonempty (CommonProfileRoomData
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data base) := by
  obtain ⟨dF, Cm⟩ := ActualHigherSOriginalDataCommonFirstWordRoom.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  let d := min base dF
  have hd : 0 < d := lt_min hbase Cm.rev.pos
  have hdBase : d ≤ base := min_le_left _ _
  have hdF : d ≤ dF := min_le_right _ _
  obtain ⟨epsG, hepsG, hepsG1, hGuard⟩ := exists_uniform_strict_higherSParam_guard
    g hg L hL y0 ρ d hd (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨{
    base_pos := hbase
    commonRadius := dF
    common := Cm
    guardRadius := d
    guardRadius_eq_min := rfl
    guardRadius_pos := hd
    guardRadius_le_base := hdBase
    guardRadius_le_common := hdF
    epsG := epsG
    epsG_pos := hepsG
    epsG_le_one := hepsG1
    members := ?_ }⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K _hK hKball F hsupp hb hs
  have hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom d := by
    intro x hx
    have hxK := hsupp hx
    have hguard := hGuard q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG x
      (ball_subset_closedBall (hKball hxK)) (hKball hxK) (hb x hxK) (hs x hxK)
    exact (higherSParam_eventually_mem y0 ρ d L dr Ar q p hdr hAr x hguard).self_of_nhds
  exact ⟨fun x hx => ⟨commonRoom_mono y0 ρ hdBase (hT x hx).1, (hT x hx).2⟩,
    fun x hx => ⟨commonRoom_mono y0 ρ hdF (hT x hx).1, (hT x hx).2⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
