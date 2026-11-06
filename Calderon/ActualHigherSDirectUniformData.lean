import Calderon.ActualHigherSDirectLowerDefinitions
import Calderon.ActualHigherSCommonProfileRoomData
import Calderon.ActualPPCoefficientCaps
import Calderon.ActualHigherSDirectAlgebra
import Calderon.ActualHigherSLinearZeroCaps
import Calderon.ActualHigherSQuadraticZeroQuarticBounds
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSPairingNormDiagnostic
import Calderon.ActualHigherSZeroAtomDictionary
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows
  ActualFullEGainedAssembly ReferenceDensityBounds ReferenceWeightedApproximation
  ActualHigherSLeadingBracketGain ConformalDepth PrincipalCommutator
  ActualHigherSLinearZero ActualHigherSQuadraticZeroWords ActualHigherSQuadraticZeroQuartic
  ActualHigherSQuadraticZeroQuarticBounds ActualHigherSLinearZeroScalarCaps
  ActualHigherSLeadingWeightedJetBounds ActualPPCoefficientCaps
  ActualScalarPrincipalSelfFormBound SectionFiveErrorForms FixedParameterProfilePullback
  ActualHigherSDirectAlgebra
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
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
  (g2 : MatrixField)
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PL" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DL" => ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "UF" => ActualHigherSFormation.higherSInput hO hD
local notation "HU" => ActualHigherSScalarCommutatorNativeForm.halfInput hO hD
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "ZH" => linearZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "TH" => linearAdjointZeroHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "QPP" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "WC" => actualWordCoefficient g L g2
local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "ParamRoom" d:max => Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d

/-- Uniform witnesses and proved native cap/room outputs, selected before profiles. -/
structure DirectUniformData where
  Mf : ℝ
  Mf_pos : 0 < Mf
  firstCaps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ data.eta0 →
    ∀ x ∈ closedBall y0 ρ, x ∈ ball y0 ρ →
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta →
    ∀ k : Fin 3,
    FirstCaps (fun y => PH dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p) Mf x ∧
    FirstCaps (fun y => PL dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p) Mf x ∧
    FirstCaps (fun y => DH dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p) Mf x ∧
    FirstCaps (fun y => DL dr Ar p q y k) (referenceRadius dr Ar p L)
      (actualReferenceBeta g L q dr Ar p) Mf x
  Cz : ℝ
  etaZ : ℝ
  Cz_pos : 0 < Cz
  etaZ_pos : 0 < etaZ
  etaZ_le_eta0 : etaZ ≤ data.eta0
  linearCaps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, ∀ hAr : 0 < Ar,
    ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 ≤ eta → eta ≤ etaZ →
    ∀ K : Set R3, IsCompact K → K ⊆ ball y0 ρ →
    ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport F.val ⊆ K →
    (∀ x ∈ K, 1 ≤ actualReferenceBeta g L q dr Ar p x) →
    (∀ x ∈ K, referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) →
    (∀ x ∈ K,
      ContDiffAt ℝ ∞ (ZH dr Ar p q) x ∧ ContDiffAt ℝ ∞ (TH dr Ar p q) x ∧
      ‖ZH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x ∧
      ‖TH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x) ∧
    ContDiff ℝ ∞ (fun x => ZH dr Ar p q x (UF F x)) ∧
    ContDiff ℝ ∞ (fun x => TH dr Ar p q x (UF F x)) ∧
    HasCompactSupport (fun x => ZH dr Ar p q x (UF F x)) ∧
    HasCompactSupport (fun x => TH dr Ar p q x (UF F x))
  Msc : ℝ
  Msc_ge_one : 1 ≤ Msc
  scalarCaps : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ dr : ℝ, ∀ hdr : 0 < dr, dr ≤ 1 → ∀ Ar : ℝ, 0 < Ar →
    ∀ p : ℕ, 1 ≤ p → ∀ x ∈ closedBall y0 ρ,
    1 ≤ actualReferenceBeta g L q dr Ar p x →
    (∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ Msc) ∧
    (∀ i k j : Fin 3, |_root_.OAI.AnisotropicCalderon.MovingFrameConnection.referenceFrameConnectionCoefficient g L q x
      (_root_.OAI.AnisotropicCalderon.SmoothMetricFrame.referenceMetricGramFrame g L (q,x) i) k j| ≤ Msc) ∧
    (∀ i : Fin 3, |referenceRadiusHorizontalLogDerivative g L q
      (referenceRadius dr Ar p L) x i| ≤ Msc*actualReferenceBeta g L q dr Ar p x) ∧
    (∀ i : Fin 3, ‖_root_.OAI.AnisotropicCalderon.SmoothMetricFrame.referenceMetricGramFrame g L (q,x) i‖ ≤ Msc) ∧
    (∀ i : Fin 3, |_root_.OAI.AnisotropicCalderon.ActualNormalizedSecondMetricDrift.normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ Msc)
  dA : ℝ
  dA_pos : 0 < dA
  dA_le_delta : dA ≤ data.δ
  dA_le_delta0 : dA ≤ data.δ0
  dA_le_rho : dA ≤ ρ
  atomRoom : ARoom dA
  Mop : ℝ
  Mop_ge_one : 1 ≤ Mop
  atomCaps : ∀ t ∈ ParamRoom dA, ∀ b : ZeroAtom,
    ‖AH t b‖ ≤ Mop ∧ ‖AL t b‖ ≤ Mop ∧ ‖RH t b‖ ≤ Mop ∧ ‖RL t b‖ ≤ Mop
  Cr : ℝ
  Cr_pos : 0 < Cr
  coordinateBound : ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 ρ,
    ∀ beta : ℝ, 1 ≤ beta → ∀ F : smoothCompactFiniteSphereCore hO hD,
    coordinateEnergyDensity coordinateDirection beta (HU F) x ≤
      Cr*finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  profileRoom : ActualHigherSQuarticFactorization.CommonProfileRoomData
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data (min data.δ dA)

local notation "DData" => DirectUniformData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2

/-- All uniform fields are produced from the unchanged original data. -/
theorem exists_direct_uniform_data (hL : 0 < L) (hKernel : UnitBallValueTraceKernel τ0)
    (hg2 : IsAdmissibleMetric g2) : Nonempty DData := by
  obtain ⟨Mf,hMf,hFirst⟩ := exists_actual_first_coefficient_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨Cz,etaZ,hCz,hetaZ,hetaZ0,hLinear⟩ := exists_linear_zero_high_contract
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hL g2 hg2
  obtain ⟨Msc,hMsc,hScalars⟩ := exists_word_scalar_caps g hg L hL y0 ρ g2 hg2
  obtain ⟨dA,hdA,hdAD,hdA0,hdArho,_hRoomA,⟨P⟩⟩ :=
    ActualAllAngularAtomGainedRoom.exists_same_packet_allAngularAtom_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data hKernel
  obtain ⟨Mop,hMop,hAtoms,_hGains⟩ := P.finiteCaps 0
  obtain ⟨Cr,hCr,hCoord⟩ := ActualHigherSScalarCommutatorNativeForm.exists_halfInput_coordinate_reference_bound
    hO hD g hg L (closedBall y0 ρ) (isCompact_closedBall _ _)
  obtain ⟨G⟩ := ActualHigherSQuarticFactorization.exists_common_profile_room_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    hL hKernel (min data.δ dA) (lt_min data.δ_pos hdA)
  refine ⟨{
    Mf := Mf, Mf_pos := hMf, firstCaps := hFirst
    Cz := Cz, etaZ := etaZ, Cz_pos := hCz, etaZ_pos := hetaZ
    etaZ_le_eta0 := hetaZ0, linearCaps := hLinear
    Msc := Msc, Msc_ge_one := hMsc, scalarCaps := hScalars
    dA := dA, dA_pos := hdA, dA_le_delta := hdAD, dA_le_delta0 := hdA0
    dA_le_rho := hdArho, atomRoom := P
    Mop := Mop, Mop_ge_one := hMop, atomCaps := ?_
    Cr := Cr, Cr_pos := hCr, coordinateBound := hCoord, profileRoom := G }⟩
  intro t ht b
  rw [ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b,
    ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b,
    ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b,
    ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b]
  simpa only [norm_iteratedFDerivWithin_zero] using hAtoms b 0 le_rfl t ht

/-- Original coefficient of the exact three direct categories. -/
def directCoefficientConstant (D : DData) : ℝ :=
  12*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*D.Mf*D.Cz*(1+D.Cr)+
  828*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*D.Cz*D.Mop^2*D.Msc^2+
  2*‖KL‖^2*D.Cz^2

/-- Positive explicit enlargement, exactly as in the original producer. -/
def directBoundConstant (D : DData) : ℝ :=
  1+directCoefficientConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D

/-- The original four restrictions precede every profile and input. -/
def directProfileThreshold (D : DData) : ℝ :=
  min data.eta0 (min D.etaZ (min 1 D.profileRoom.epsG))

lemma directCoefficientConstant_nonneg (D : DData) :
    0 ≤ directCoefficientConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D := by
  have hMf : 0 ≤ D.Mf := D.Mf_pos.le
  have hCz : 0 ≤ D.Cz := D.Cz_pos.le
  have hCr : 0 ≤ D.Cr := D.Cr_pos.le
  have hN := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  dsimp only [directCoefficientConstant]
  positivity

lemma directBoundConstant_pos (D : DData) :
    0 < directBoundConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D := by
  have h := directCoefficientConstant_nonneg g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  dsimp only [directBoundConstant]
  linarith

lemma directCoefficientConstant_le_bound (D : DData) :
    directCoefficientConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D ≤
    directBoundConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D := by
  dsimp only [directBoundConstant]
  linarith

lemma directProfileThreshold_pos (D : DData) :
    0 < directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D := by
  exact lt_min data.eta0_pos (lt_min D.etaZ_pos (lt_min zero_lt_one D.profileRoom.epsG_pos))

lemma directProfileThreshold_bounds (D : DData) :
    directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D ≤ data.eta0 ∧
    directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D ≤ D.etaZ ∧
    directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D ≤ 1 ∧
    directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D ≤ D.profileRoom.epsG := by
  exact ⟨min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
