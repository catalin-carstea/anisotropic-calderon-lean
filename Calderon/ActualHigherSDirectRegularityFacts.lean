import Calderon.ActualHigherSDirectLowerDefinitions
import Calderon.ActualHigherSDirectUniformData
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

local notation "ZO" => actualZ1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "TO" => actualT1Out g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2

local notation "DF" => directFirstLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DQ" => directQuadraticLinear g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "DS" => directLinearSquares g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2
local notation "DR" => actualDirectLower g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  atomHigh atomLow atomReverseHigh atomReverseLow

local notation "DData" => DirectUniformData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "etaD" D:max => directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D

/-- Complete proved regularity and original-input support facts for an actual physical map. -/
structure DirectPhysicalMapFacts (F : smoothCompactFiniteSphereCore hO hD) (f : R3 → SphereL2) : Prop where
  smooth : ContDiff ℝ ∞ f
  compact : HasCompactSupport f
  off_input : ∀ x ∉ tsupport F.val,f x=0

/-- Exact finite lift regularity and zero outside the ORIGINAL input support. -/
lemma actual_direct_input_facts (F : smoothCompactFiniteSphereCore hO hD) :
    ContDiff ℝ ∞ (UF F) ∧ ∀ x ∉ tsupport F.val,UF F x=0 := by
  constructor
  · simpa only [ActualHigherSFormation.higherSInput] using
      contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  · intro x hx
    simpa only [ActualHigherSFormation.higherSInput] using
      ActualHigherSFormation.finiteCoreSobolevLift_eq_zero_of_eval hO hD (3/2 : ℝ) F x
        (image_eq_zero_of_notMem_tsupport hx)

lemma actual_direct_input_derivative_off (F : smoothCompactFiniteSphereCore hO hD)
    (k : Fin 3) (x : R3) (hx : x ∉ tsupport F.val) :
    directionalFDeriv (coordinateDirection k) (UF F) x=0 := by
  exact ActualHigherSScalarCommutatorForm.directional_eq_zero_off
    (UF F) (tsupport F.val) (isClosed_tsupport F.val)
    (actual_direct_input_facts hO hD F).2 (coordinateDirection k) x hx

private lemma compact_of_input_zero {V : Type*} [Zero V]
    (F : smoothCompactFiniteSphereCore hO hD) (f : R3 → V)
    (K : Set R3) (hK : IsCompact K) (hsupp : tsupport F.val ⊆ K)
    (hf : ∀ x ∉ tsupport F.val,f x=0) : HasCompactSupport f := by
  exact HasCompactSupport.intro hK (fun x hx => hf x (fun hxi => hx (hsupp hxi)))

/-- BOTH complete actual first outputs, without word/linear proof contexts. -/
lemma actual_direct_first_output_facts
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    DirectPhysicalMapFacts hO hD F (PF dr Ar p q F) ∧
    DirectPhysicalMapFacts hO hD F (PR dr Ar p q F) := by
  have hth := directProfileThreshold_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have heta0 : eta ≤ data.eta0 := hetaD.trans hth.1
  let U := UF F
  let dU := fun k : Fin 3 => directionalFDeriv (coordinateDirection k) U
  have hU : ContDiff ℝ ∞ U := (actual_direct_input_facts hO hD F).1
  have hdUs (k : Fin 3) : ContDiff ℝ ∞ (dU k) := contDiff_directionalFDeriv _ U hU
  have hdU0 (k : Fin 3) (x : R3) (hx : x ∉ tsupport F.val) : dU k x=0 :=
    actual_direct_input_derivative_off hO hD F k x hx
  have hdUK (k : Fin 3) : ∀ x ∉ K,dU k x=0 :=
    fun x hx => hdU0 k x (fun hxi => hx (hsupp hxi))
  have hfc (k : Fin 3) (x : R3) (hx : x ∈ K) :=
    D.firstCaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x
      (ball_subset_closedBall (hKball hx)) (hKball hx) (hb x hx) (hs x hx) k
  have hPHs (k : Fin 3) : ContDiff ℝ ∞ (fun x => PH dr Ar p q x k (dU k x)) :=
    ActualHigherSScalarCommutatorForm.contDiff_supported_operator_apply (dU k) _ K hK.isClosed
      (hdUs k) (hdUK k) (fun x hx => (hfc k x hx).1.1)
  have hDHs (k : Fin 3) : ContDiff ℝ ∞ (fun x => DH dr Ar p q x k (dU k x)) :=
    ActualHigherSScalarCommutatorForm.contDiff_supported_operator_apply (dU k) _ K hK.isClosed
      (hdUs k) (hdUK k) (fun x hx => (hfc k x hx).2.2.1.1)
  have hPFs : ContDiff ℝ ∞ (PF dr Ar p q F) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp (ContDiff.sum (fun k _ => hPHs k))
  have hPRs : ContDiff ℝ ∞ (PR dr Ar p q F) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp (ContDiff.sum (fun k _ => hDHs k))
  have hPF0 (x : R3) (hx : x ∉ tsupport F.val) : PF dr Ar p q F x=0 := by
    change KL (∑ k : Fin 3, PH dr Ar p q x k (dU k x))=0
    have hz : (∑ k : Fin 3, PH dr Ar p q x k (dU k x))=0 :=
      Finset.sum_eq_zero (fun k _ => by rw [hdU0 k x hx,map_zero])
    exact (congrArg (fun v : Half => KL v) hz).trans (map_zero KL)
  have hPR0 (x : R3) (hx : x ∉ tsupport F.val) : PR dr Ar p q F x=0 := by
    change KL (∑ k : Fin 3, DH dr Ar p q x k (dU k x))=0
    have hz : (∑ k : Fin 3, DH dr Ar p q x k (dU k x))=0 :=
      Finset.sum_eq_zero (fun k _ => by rw [hdU0 k x hx,map_zero])
    exact (congrArg (fun v : Half => KL v) hz).trans (map_zero KL)
  exact ⟨⟨hPFs,compact_of_input_zero hO hD F _ K hK hsupp hPF0,hPF0⟩,
    ⟨hPRs,compact_of_input_zero hO hD F _ K hK hsupp hPR0,hPR0⟩⟩

/-- BOTH complete actual quadratic outputs. Zero proofs use typed equality transport. -/
lemma actual_direct_word_output_facts (hg2 : IsAdmissibleMetric g2)
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    DirectPhysicalMapFacts hO hD F (fun x => KL (Z2 dr Ar p q F x)) ∧
    DirectPhysicalMapFacts hO hD F (fun x => KL (T2 dr Ar p q F x)) := by
  have hth := directProfileThreshold_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have hetaG : eta ≤ D.profileRoom.epsG := hetaD.trans hth.2.2.2
  have hmem := D.profileRoom.members q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hsupp hb hs
  have hWord := actualZ2T2_contDiff_support
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    D.profileRoom.commonRadius D.profileRoom.common g2 hg2 dr Ar p hdr hAr q F hmem.2
  have hZ0 (x : R3) (hx : x ∉ tsupport F.val) : Z2 dr Ar p q F x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hzx => hx (hWord.2.2.1 hzx))
  have hT0 (x : R3) (hx : x ∉ tsupport F.val) : T2 dr Ar p q F x=0 :=
    image_eq_zero_of_notMem_tsupport (fun htx => hx (hWord.2.2.2 htx))
  have hKZ0 (x : R3) (hx : x ∉ tsupport F.val) : KL (Z2 dr Ar p q F x)=0 :=
    (congrArg (fun v : Half => KL v) (hZ0 x hx)).trans (map_zero KL)
  have hKT0 (x : R3) (hx : x ∉ tsupport F.val) : KL (T2 dr Ar p q F x)=0 :=
    (congrArg (fun v : Half => KL v) (hT0 x hx)).trans (map_zero KL)
  exact ⟨⟨(sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hWord.1,
      compact_of_input_zero hO hD F _ K hK hsupp hKZ0,hKZ0⟩,
    ⟨(sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hWord.2.1,
      compact_of_input_zero hO hD F _ K hK hsupp hKT0,hKT0⟩⟩

/-- BOTH complete actual linear outputs. -/
lemma actual_direct_linear_output_facts
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    DirectPhysicalMapFacts hO hD F (ZO dr Ar p q F) ∧
    DirectPhysicalMapFacts hO hD F (TO dr Ar p q F) := by
  have hth := directProfileThreshold_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have hetaZ : eta ≤ D.etaZ := hetaD.trans hth.2.1
  have hLin := D.linearCaps q hq dr hdr hdr1 Ar hAr p hp eta heta hetaZ K hK hKball F hsupp hb hs
  have hZO0 (x : R3) (hx : x ∉ tsupport F.val) : ZO dr Ar p q F x=0 := by
    change KL (ZH dr Ar p q x (UF F x))=0
    rw [(actual_direct_input_facts hO hD F).2 x hx,map_zero,map_zero]
  have hTO0 (x : R3) (hx : x ∉ tsupport F.val) : TO dr Ar p q F x=0 := by
    change KL (TH dr Ar p q x (UF F x))=0
    rw [(actual_direct_input_facts hO hD F).2 x hx,map_zero,map_zero]
  exact ⟨⟨(sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hLin.2.1,
      compact_of_input_zero hO hD F _ K hK hsupp hZO0,hZO0⟩,
    ⟨(sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hLin.2.2.1,
      compact_of_input_zero hO hD F _ K hK hsupp hTO0,hTO0⟩⟩

/-- Continuous compactly supported weighted scalar integration, at its full small goal. -/
private lemma direct_weighted_integrable (hg : IsAdmissibleMetric g) (q : ℝ) (K : Set R3) (hK : IsCompact K)
    (f : R3 → ℝ) (hf : Continuous f) (hf0 : ∀ x ∉ K,f x=0) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*f x) := by
  have hmu : Continuous (fun x : R3 => referenceDensityFamily g L (q,x)) :=
    (contDiff_referenceDensityFamily g hg L).continuous.comp (continuous_const.prodMk continuous_id)
  apply (hmu.mul hf).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro hK
  intro x hx
  change referenceDensityFamily g L (q,x)*f x=0
  rw [hf0 x hx,mul_zero]

/-- Complete regularity, off-input zero and all SIX original integrabilities. -/
structure DirectRegularityFacts (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) : Prop where
  regularity : DirectPhysicalRegularity g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F
  first_off_input : ∀ x ∉ tsupport F.val,PF dr Ar p q F x=0
  reverse_first_off_input : ∀ x ∉ tsupport F.val,PR dr Ar p q F x=0
  quadratic_off_input : ∀ x ∉ tsupport F.val,KL (Z2 dr Ar p q F x)=0
  reverse_quadratic_off_input : ∀ x ∉ tsupport F.val,KL (T2 dr Ar p q F x)=0
  linear_off_input : ∀ x ∉ tsupport F.val,ZO dr Ar p q F x=0
  reverse_linear_off_input : ∀ x ∉ tsupport F.val,TO dr Ar p q F x=0
  direct_off_input : ∀ x ∉ tsupport F.val,DR dr Ar p q F x=0
  first_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*DF dr Ar p q F x)
  quadratic_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*DQ dr Ar p q F x)
  squares_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*DS dr Ar p q F x)
  direct_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*DR dr Ar p q F x)
  absolute_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*|DR dr Ar p q F x|)
  energy_integrable : Integrable (fun x => referenceDensityFamily g L (q,x)*
    finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
  energy_nonneg : ∀ x,0 ≤ referenceDensityFamily g L (q,x)*
    finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x

/-- A complete native energy L1 proof, separated from six-map assembly. -/
lemma actual_direct_energy_facts (hL : 0 < L) (hg2 : IsAdmissibleMetric g2)
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x) ∧
    ∀ x,0 ≤ referenceDensityFamily g L (q,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  have hth := directProfileThreshold_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have heta0 : eta ≤ data.eta0 := hetaD.trans hth.1
  obtain ⟨_CLead,_hCLead,hLeading⟩ := exists_actual_leading_signed_second_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hL hreg data g2 hg2
  refine ⟨(hLeading q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 K hK hKball F hsupp hb hs).2.1,?_⟩
  intro x
  have hbpos := actualReferenceBeta_pos g hg L q dr Ar p hL hdr hAr hp x
  exact mul_nonneg (referenceDensityFamily_pos g hg L (q,x)).le
    (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q _ hbpos.le F x)

/-- All actual map facts are produced; no external regularity or analytic callback. -/
lemma actual_direct_regularity_facts (hL : 0 < L) (hg2 : IsAdmissibleMetric g2)
    (D : DData) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1) (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) : DirectRegularityFacts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F := by
  have hFirst := actual_direct_first_output_facts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  have hWord := actual_direct_word_output_facts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  have hLinear := actual_direct_linear_output_facts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  have hDFs : Continuous (DF dr Ar p q F) := continuous_const.mul
    ((hFirst.1.smooth.continuous.inner hLinear.1.smooth.continuous).sub
      (hFirst.2.smooth.continuous.inner hLinear.2.smooth.continuous))
  have hDQs : Continuous (DQ dr Ar p q F) := continuous_const.mul
    ((hWord.1.smooth.continuous.inner hLinear.1.smooth.continuous).sub
      (hWord.2.smooth.continuous.inner hLinear.2.smooth.continuous))
  have hDSs : Continuous (DS dr Ar p q F) :=
    (hLinear.1.smooth.continuous.norm.pow 2).sub (hLinear.2.smooth.continuous.norm.pow 2)
  have hDRs : Continuous (DR dr Ar p q F) := (hDFs.add hDQs).add hDSs
  have hDF0 (x : R3) (hx : x ∉ tsupport F.val) : DF dr Ar p q F x=0 := by
    simp only [directFirstLinear,hLinear.1.off_input x hx,hLinear.2.off_input x hx,
      inner_zero_right,sub_self,mul_zero]
  have hDQ0 (x : R3) (hx : x ∉ tsupport F.val) : DQ dr Ar p q F x=0 := by
    simp only [directQuadraticLinear,hLinear.1.off_input x hx,hLinear.2.off_input x hx,
      inner_zero_right,sub_self,mul_zero]
  have hDS0 (x : R3) (hx : x ∉ tsupport F.val) : DS dr Ar p q F x=0 := by
    simp only [directLinearSquares,hLinear.1.off_input x hx,hLinear.2.off_input x hx,
      norm_zero,sub_self]
  have hDR0 (x : R3) (hx : x ∉ tsupport F.val) : DR dr Ar p q F x=0 := by
    simp only [actualDirectLower,hDF0 x hx,hDQ0 x hx,hDS0 x hx,add_zero]
  have hEnergy := actual_direct_energy_facts g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hL hg2 D q hq dr hdr hdr1 Ar hAr p hp eta heta hetaD K hK hKball F hsupp hb hs
  refine {
    regularity := ⟨⟨hFirst.1.smooth,hFirst.1.compact⟩,⟨hFirst.2.smooth,hFirst.2.compact⟩,
      ⟨hWord.1.smooth,hWord.1.compact⟩,⟨hWord.2.smooth,hWord.2.compact⟩,
      ⟨hLinear.1.smooth,hLinear.1.compact⟩,⟨hLinear.2.smooth,hLinear.2.compact⟩⟩
    first_off_input := hFirst.1.off_input, reverse_first_off_input := hFirst.2.off_input
    quadratic_off_input := hWord.1.off_input, reverse_quadratic_off_input := hWord.2.off_input
    linear_off_input := hLinear.1.off_input, reverse_linear_off_input := hLinear.2.off_input
    direct_off_input := hDR0
    first_integrable := direct_weighted_integrable g L hg q K hK _ hDFs ?_
    quadratic_integrable := direct_weighted_integrable g L hg q K hK _ hDQs ?_
    squares_integrable := direct_weighted_integrable g L hg q K hK _ hDSs ?_
    direct_integrable := direct_weighted_integrable g L hg q K hK _ hDRs ?_
    absolute_integrable := direct_weighted_integrable g L hg q K hK _ hDRs.abs ?_
    energy_integrable := hEnergy.1, energy_nonneg := hEnergy.2 }
  · exact fun x hx => hDF0 x (fun hxi => hx (hsupp hxi))
  · exact fun x hx => hDQ0 x (fun hxi => hx (hsupp hxi))
  · exact fun x hx => hDS0 x (fun hxi => hx (hsupp hxi))
  · exact fun x hx => hDR0 x (fun hxi => hx (hsupp hxi))
  · intro x hx
    rw [hDR0 x (fun hxi => hx (hsupp hxi)),abs_zero]
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
