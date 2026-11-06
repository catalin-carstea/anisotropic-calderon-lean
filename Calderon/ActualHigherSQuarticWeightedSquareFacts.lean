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

/-! Regularity and support, and both weighted square integrabilities, for the quartic
factorization. -/
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

/-- Smoothness, support and both L1 square facts at one profile. -/
structure WeightedSquareFacts (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) : Prop where
  regularZ : ContDiff ℝ ∞ (Z2 g2 dr Ar p q F)
  regularT : ContDiff ℝ ∞ (T2 g2 dr Ar p q F)
  supportZ : tsupport (Z2 g2 dr Ar p q F) ⊆ tsupport F.val
  supportT : tsupport (T2 g2 dr Ar p q F) ⊆ tsupport F.val
  integrableZ : Integrable
    (fun x => referenceDensityFamily g L (q,x)*‖KL (Z2 g2 dr Ar p q F x)‖^2)
  integrableT : Integrable
    (fun x => referenceDensityFamily g L (q,x)*‖KL (T2 g2 dr Ar p q F x)‖^2)

/-- The complete facts, from the native room and support membership. -/
lemma weighted_square_facts_of_original_room (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (K : Set R3) (hK : IsCompact K)
    (hsupp : tsupport F.val ⊆ K)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    WeightedSquareFacts
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      g2 dr Ar p q F := by
  have hReg := ActualHigherSQuadraticZeroQuarticBounds.actualZ2T2_contDiff_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm g2 hg2 dr Ar p hdr hAr q F hTF
  have hCptZ : HasCompactSupport (Z2 g2 dr Ar p q F) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hReg.2.2.1.trans hsupp)
  have hCptT : HasCompactSupport (T2 g2 dr Ar p q F) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hReg.2.2.2.trans hsupp)
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  have hIZ := integrable_weighted_norm_sq_of_continuous_compact
    (fun x : R3 => referenceDensityFamily g L (q,x)) hmu
    (fun x => KL (Z2 g2 dr Ar p q F x))
    ((KL).continuous.comp hReg.1.continuous) (hCptZ.comp_left (map_zero KL))
  have hIT := integrable_weighted_norm_sq_of_continuous_compact
    (fun x : R3 => referenceDensityFamily g L (q,x)) hmu
    (fun x => KL (T2 g2 dr Ar p q F x))
    ((KL).continuous.comp hReg.2.1.continuous) (hCptT.comp_left (map_zero KL))
  exact ⟨hReg.1, hReg.2.1, hReg.2.2.1, hReg.2.2.2, hIZ, hIT⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
