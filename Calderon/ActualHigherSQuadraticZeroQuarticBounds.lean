import Calderon.ActualHigherSQuarticIdentityRowData
import Calderon.ActualHigherSCommonProfileRoomData
import Calderon.ActualHigherSQuarticWeightedSquareFacts
import Calderon.ActualHigherSQuarticPointwiseBound
import Calderon.ActualHigherSQuarticIntegralTransfer
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

/-! Complete actual207-word quartic uniform estimate, author source UNCOMPILED.
Own conditional source interfaces are not native/provider grants. Scalar cap
producer758c6aa5 was consumed ONLY through its exact declaration and upfront,
under Root's explicit conditional-interface grant; no new proof body was read.
No analytic callback escapes the final theorem. Original source/body/API/owner/
norm/literature-relative37 holds and pending human ratification remain. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
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

theorem exists_uniform_same_packet_actual207_quartic_bound
    (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) :
    ∃ Cquart etaQuart : ℝ, 0 < Cquart ∧ 0 < etaQuart ∧ etaQuart ≤ data.eta0 ∧
      ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
      ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaQuart →
      ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
      (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2) ∧
      (∀ x ∈ K,
        |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| ≤
          Cquart*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
            (actualReferenceBeta g L q dr Ar p x) F x) ∧
      |(∫ x, referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2) -
        (∫ x, referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2)| ≤
        Cquart*eta*(∫ x, referenceDensityFamily g L (q,x)*finiteCoreReferenceProfileEnergy
          hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) := by
  let I := Classical.choice (ActualHigherSQuarticFactorization.exists_identity_row_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel g2)
  let scalarCaps := ActualHigherSLinearZeroScalarCaps.exists_word_scalar_caps
    g hg L hL y0 ρ g2 hg2
  let Msc := Classical.choose scalarCaps
  have hMsc : 1 ≤ Msc := (Classical.choose_spec scalarCaps).1
  have hScalars := (Classical.choose_spec scalarCaps).2
  let G := Classical.choice (ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel I.dI I.dI_pos)
  let leading := ActualFullEGainedAssembly.exists_actual_leading_signed_second_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  have hLeading := (Classical.choose_spec leading).2
  let Mop := I.Mop
  have hMop : 1 ≤ Mop := I.Mop_ge_one
  let Dquart := (207 : ℝ)^2*Msc^4*(4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3)
  let Cquart := 1+Dquart
  let etaQuart := min data.eta0 (min 1 G.epsG)
  have hMop0 : 0 ≤ Mop := zero_le_one.trans hMop
  have hMsc0 : 0 ≤ Msc := zero_le_one.trans hMsc
  have hPairingNorm : 0 ≤ (ActualHigherSPairingNormDiagnostic.standardPairingNorm PL) :=
    ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hDquart : 0 ≤ Dquart := by
    change 0 ≤ (207 : ℝ)^2*Msc^4*(4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hMsc0 _))
      (mul_nonneg (mul_nonneg (by norm_num) hPairingNorm) (pow_nonneg hMop0 _))
  have hCquart : 0 < Cquart := by dsimp [Cquart]; linarith
  refine ⟨Cquart, etaQuart, hCquart,
    lt_min data.eta0_pos (lt_min zero_lt_one G.epsG_pos), min_le_left _ _, ?_⟩
  intro q hq dr hdr hdr1 Ar hAr p hp eta heta hetaQuart K hK hKball F hsupp hb hs
  have heta0 : eta ≤ data.eta0 := hetaQuart.trans (min_le_left _ _)
  have heta1 : eta ≤ 1 := hetaQuart.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetaG : eta ≤ G.epsG := hetaQuart.trans ((min_le_right _ _).trans (min_le_right _ _))
  have rooms := G.members q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hsupp hb hs
  have squares := ActualHigherSQuarticFactorization.weighted_square_facts_of_original_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    G.commonRadius G.common g2 hg2 dr Ar p hdr hAr q F K hK hsupp rooms.2
  have hPoint := ActualHigherSQuarticFactorization.pointwise_defect_le_reference_energy
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    g2 I Msc hMsc hScalars dr Ar p hdr hdr1 hAr hp q hq eta heta heta1
    K hKball F hb hs rooms.1 squares.supportZ squares.supportT
  have hLeadingFacts := hLeading q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs
  have hIE := hLeadingFacts.2.1
  have hIntegral := ActualHigherSQuarticFactorization.integral_defect_le_reference_energy
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL g2 dr Ar p hdr hAr hp q Cquart eta hCquart heta K F hsupp
    squares.supportZ squares.supportT squares.integrableZ squares.integrableT hPoint hIE
  exact ⟨squares.integrableZ, squares.integrableT, hPoint, hIntegral⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
