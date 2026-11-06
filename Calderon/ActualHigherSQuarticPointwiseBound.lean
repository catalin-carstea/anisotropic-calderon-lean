import Calderon.ActualHigherSQuarticIdentityRowData
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

/-! The pointwise norm-defect estimate for the square of the 207-word family. -/
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

/-- Full support/off-support quartic point estimate at the actual original profile. -/
lemma pointwise_defect_le_reference_energy (g2 : MatrixField)
    (I : IdentityRowData
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2)
    (Msc : ℝ) (hMsc : 1 ≤ Msc)
    (hScalars : ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ closedBall y0 ρ,
      1 ≤ actualReferenceBeta g L q dr Ar p x →
      (∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ Msc) ∧
      (∀ i k j : Fin 3, |referenceFrameConnectionCoefficient g L q x
        (referenceMetricGramFrame g L (q,x) i) k j| ≤ Msc) ∧
      (∀ i : Fin 3, |referenceRadiusHorizontalLogDerivative g L q
        (referenceRadius dr Ar p L) x i| ≤ Msc*actualReferenceBeta g L q dr Ar p x) ∧
      (∀ i : Fin 3, ‖referenceMetricGramFrame g L (q,x) i‖ ≤ Msc) ∧
      (∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Msc))
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (hAr : 0 < Ar)
    (hp : 1 ≤ p) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (eta : ℝ) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (K : Set R3) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hb : ∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta)
    (hTI : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom I.dI)
    (hZS : tsupport (Z2 g2 dr Ar p q F) ⊆ tsupport F.val)
    (hTS : tsupport (T2 g2 dr Ar p q F) ⊆ tsupport F.val) :
    ∀ x ∈ K,
      |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| ≤
        (1+(207 : ℝ)^2*Msc^4*
          (4*ActualHigherSPairingNormDiagnostic.standardPairingNorm PL*I.Mop^3))*eta*
            finiteCoreReferenceProfileEnergy hO hD g hg L q
              (actualReferenceBeta g L q dr Ar p x) F x := by
  let dA := I.dA
  let P := I.packet
  let dI := I.dI
  let Mop := I.Mop
  have hMop : 1 ≤ Mop := I.Mop_ge_one
  have hdIA : dI ≤ dA := I.dI_le_dA
  have hIdentity := I.identity
  have hRows := I.rows
  let Dquart := (207 : ℝ)^2*Msc^4*(4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3)
  let Cquart := 1+Dquart
  have hMop0 : 0 ≤ Mop := zero_le_one.trans hMop
  have hMsc0 : 0 ≤ Msc := zero_le_one.trans hMsc
  have hPairingNorm : 0 ≤ (ActualHigherSPairingNormDiagnostic.standardPairingNorm PL) :=
    ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hDquart : 0 ≤ Dquart := by
    change 0 ≤ (207 : ℝ)^2*Msc^4*(4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hMsc0 _))
      (mul_nonneg (mul_nonneg (by norm_num) hPairingNorm) (pow_nonneg hMop0 _))
  have hCquart : 0 < Cquart := by dsimp [Cquart]; linarith
  change ∀ x ∈ K,
    |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| ≤
      Cquart*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x
  intro x hxK
  by_cases hx : x ∈ tsupport F.val
  · let r := referenceRadius dr Ar p L x
    let beta := actualReferenceBeta g L q dr Ar p x
    let U := UF F x
    let t := (Tq dr Ar p q) x
    have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
    have hbX : 1 ≤ beta := hb x hxK
    have hsX : r*beta^2 ≤ eta := hs x hxK
    have htA : t ∈ ParamRoom dA :=
      ⟨commonRoom_mono y0 ρ hdIA (hTI x hx).1, (hTI x hx).2⟩
    have hS := hScalars q hq dr hdr hdr1 Ar hAr p hp x
      (ball_subset_closedBall (hKball hxK)) hbX
    have hΓ (i a b : Fin 3) :
        |ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t| ≤ Msc := by
      simpa only [ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
        ActualHigherSZeroCoefficientFactorisation.parameterGramFrame,
        ActualHigherSFormation.higherSParam, t] using hS.2.1 i a b
    have hc (z : ZeroWord) : |WC g2 dr Ar p q x z| ≤ Msc^2*r :=
      ActualHigherSQuadraticZeroQuarticBounds.abs_wordCoefficient_le_common r beta Msc
        (referenceDensityPrincipalFrameCoefficient g g2 L q x)
        (referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x)
        (fun i a b => ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b t)
        hr hbX hMsc (hsX.trans heta1) hS.1 hS.2.2.1 hΓ z
    have hRaw := ActualHigherSQuarticBound.abs_weighted_word_sum_le
      (WC g2 dr Ar p q x) (fun z v => QR P t U z v) (Msc^2) r
      (4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3*‖U‖^2) (sq_nonneg Msc) hr (by positivity) hc
      (fun z v => hRows t htA U z v)
    rw [card_zeroWord] at hRaw
    have hDefect :
        |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| ≤
          Cquart*r^2*‖U‖^2 := by
      rw [hIdentity dr Ar p hdr hAr q F hTI x]
      calc
        _ ≤ (207 : ℝ)^2*(Msc^2)^2*r^2*(4*(ActualHigherSPairingNormDiagnostic.standardPairingNorm PL)*Mop^3*‖U‖^2) := hRaw
        _ = Dquart*r^2*‖U‖^2 := by dsimp [Dquart]; ring
        _ ≤ Cquart*r^2*‖U‖^2 := by
          gcongr
          dsimp [Cquart]
          linarith
    have hEnergy := ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
      g L hg hO hD q beta (zero_le_one.trans hbX) F x
    have hAbsorb := ActualHigherSQuarticBound.radius_sq_energy_absorption
      r beta eta (finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x) ‖U‖
      hr hbX heta heta1 hsX hEnergy
    calc
      _ ≤ Cquart*(r^2*‖U‖^2) := by simpa only [mul_assoc] using hDefect
      _ ≤ Cquart*(eta*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x) :=
        mul_le_mul_of_nonneg_left hAbsorb hCquart.le
      _ = _ := by ring
  · have hZ0 : Z2 g2 dr Ar p q F x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hZS h))
    have hT0 : T2 g2 dr Ar p q F x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hTS h))
    have hDefect0 : ‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2 = 0 :=
      ActualHigherSZeroAtomTransport.sub_values_eq_sum_of_both_eq_zero
        (fun Z : Half => ‖KL Z‖^2) hZ0 hT0 (rfl : (0 : ℝ) = 0)
    have hAbs0 : |‖KL (Z2 g2 dr Ar p q F x)‖^2-‖KL (T2 g2 dr Ar p q F x)‖^2| = 0 :=
      (congrArg abs hDefect0).trans abs_zero
    have hE := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) (zero_le_one.trans (hb x hxK)) F x
    exact hAbs0.le.trans (mul_nonneg (mul_nonneg hCquart.le heta) hE)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticFactorization
