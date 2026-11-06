import Calderon.ActualHigherSDirectFirstLinearBound
import Calderon.ActualHigherSDirectQuadraticLinearBound
import Calderon.ActualHigherSDirectLinearSquaresBound
import Calderon.ActualHigherSDirectAtomGraphs
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

/-- Typed point estimate. Every intermediate cap, room and lift premise is
produced from the original packet in exists_actual_direct_lower below. -/
lemma actual_direct_point_of_caps {dA : ℝ} (P : ARoom dA)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (htA : (Tq dr Ar p q) x ∈ ParamRoom dA)
    (Mf Cz Mop Msc Cr eta : ℝ)
    (hMf : 0 ≤ Mf) (hCz : 0 ≤ Cz) (hMop : 0 ≤ Mop) (hMsc : 0 ≤ Msc) (hCr : 0 ≤ Cr)
    (heta : 0 ≤ eta)
    (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hLow : ∀ k : Fin 3,‖PL dr Ar p q x k‖ ≤ Mf*(referenceRadius dr Ar p L x)^2 ∧
      ‖DL dr Ar p q x k‖ ≤ Mf*(referenceRadius dr Ar p L x)^2)
    (hLin : ‖ZH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x ∧
      ‖TH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x)
    (hAtoms : ∀ a : ZeroAtom,‖AH ((Tq dr Ar p q) x) a‖ ≤ Mop ∧
      ‖AL ((Tq dr Ar p q) x) a‖ ≤ Mop ∧ ‖RH ((Tq dr Ar p q) x) a‖ ≤ Mop ∧
      ‖RL ((Tq dr Ar p q) x) a‖ ≤ Mop)
    (hLifts : (∀ a : ZeroAtom,IH (VA dr Ar p q F x a)=AH ((Tq dr Ar p q) x) a (UF F x)) ∧
      (∀ a : ZeroAtom,IH (VB dr Ar p q F x a)=RH ((Tq dr Ar p q) x) a (UF F x)))
    (hc : ∀ z : ZeroWord,|WC dr Ar p q x z| ≤ Msc^2*referenceRadius dr Ar p L x)
    (hYoung : ∀ k : Fin 3,‖directionalFDeriv (coordinateDirection k) (HU F) x‖*‖UF F x‖ ≤
      (1+Cr)*finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q dr Ar p x) F x)
    (hHigh : actualReferenceBeta g L q dr Ar p x*‖UF F x‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
    (hr : 0 ≤ referenceRadius dr Ar p L x)
    (h3 : (referenceRadius dr Ar p L x)^3 ≤ eta)
    (h4 : (referenceRadius dr Ar p L x)^4*actualReferenceBeta g L q dr Ar p x ≤ eta) :
    |DR dr Ar p q F x| ≤
      (12*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Mf*Cz*(1+Cr)+828*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Cz*Mop^2*Msc^2+
        2*‖KL‖^2*Cz^2)*eta*finiteCoreReferenceProfileEnergy hO hD g hg L q
          (actualReferenceBeta g L q dr Ar p x) F x := by
  have hFirst := actual_direct_first_linear_of_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x htD
    Mf Cz Cr eta hMf hCz hCr heta hb hLow hLin hYoung hr h4
  have hQuad := actual_direct_quadratic_linear_of_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 P dr Ar p q F x htA
    Cz Mop Msc eta hCz hMop hMsc heta hb hLin hAtoms hLifts hc hHigh hr h3
  have hSquares := actual_direct_linear_squares_of_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x Cz eta hCz heta hb hLin hHigh hr h4
  exact (abs_three_sum_le _ _ _).trans
    ((add_le_add (add_le_add hFirst hQuad) hSquares).trans (le_of_eq (by ring)))

local notation "DData" => DirectUniformData g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2
local notation "C0" D:max => directCoefficientConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
local notation "CD" D:max => directBoundConstant g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
local notation "etaD" D:max => directProfileThreshold g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D

/-- Actual complete profile specialization on the original input support.
The full original K extension follows from the separately proved off-input zero facts. -/
lemma actual_direct_pointwise_on_input_support (D : DData)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (dr : ℝ) (hdr : 0 < dr) (hdr1 : dr ≤ 1)
    (Ar : ℝ) (hAr : 0 < Ar) (p : ℕ) (hp : 1 ≤ p)
    (eta : ℝ) (heta : 0 ≤ eta) (hetaD : eta ≤ etaD D)
    (K : Set R3) (hK : IsCompact K) (hKball : K ⊆ ball y0 ρ)
    (F : smoothCompactFiniteSphereCore hO hD) (hsupp : tsupport F.val ⊆ K)
    (hb : ∀ x ∈ K,1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hs : ∀ x ∈ K,referenceRadius dr Ar p L x*(actualReferenceBeta g L q dr Ar p x)^2 ≤ eta) :
    ∀ x ∈ tsupport F.val, |DR dr Ar p q F x| ≤ CD D*eta*
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x := by
  have hth := directProfileThreshold_bounds g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  have heta0 : eta ≤ data.eta0 := hetaD.trans hth.1
  have hetaZ : eta ≤ D.etaZ := hetaD.trans hth.2.1
  have heta1 : eta ≤ 1 := hetaD.trans hth.2.2.1
  have hetaG : eta ≤ D.profileRoom.epsG := hetaD.trans hth.2.2.2
  have hmem := D.profileRoom.members q hq dr hdr hdr1 Ar hAr p hp eta heta hetaG K hK hKball F hsupp hb hs
  have hTF := hmem.2
  have hLifts := actualAtomHi_inclusions
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    D.profileRoom.commonRadius D.profileRoom.common dr Ar p hdr hAr q F hTF
  intro x hxI
  have hx : x ∈ K := hsupp hxI
  have hxClosed : x ∈ closedBall y0 ρ := ball_subset_closedBall (hKball hx)
  have hfc (k : Fin 3) := D.firstCaps q hq dr hdr hdr1 Ar hAr p hp eta heta heta0 x hxClosed (hKball hx) (hb x hx) (hs x hx) k
  have hLin := (D.linearCaps q hq dr hdr hdr1 Ar hAr p hp eta heta hetaZ K hK hKball F hsupp hb hs).1 x hx
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let E := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  let du := fun k : Fin 3 => directionalFDeriv (coordinateDirection k) (HU F) x
  have hr : 0 ≤ r := (referenceRadius_pos dr Ar p L x hdr hAr).le
  have hbX : 1 ≤ beta := hb x hx
  have hb0 : 0 ≤ beta := zero_le_one.trans hbX
  have hbpos : 0 < beta := zero_lt_one.trans_le hbX
  have hEX : 0 ≤ E := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q beta hb0 F x
  have hsX : r*beta^2 ≤ eta := hs x hx
  have hbeta2 : 1 ≤ beta^2 := by nlinarith only [hbX]
  have hrEta : r ≤ eta := by nlinarith only [hsX,mul_nonneg hr (sub_nonneg.mpr hbeta2)]
  have hr1 : r ≤ 1 := hrEta.trans heta1
  have hr2 : r^2 ≤ r := by nlinarith only [hr,hr1]
  have hr3 : r^3 ≤ eta := by
    have hh := mul_le_mul_of_nonneg_right hr2 hr
    nlinarith only [hh,hr2,hrEta]
  have hr4 : r^4*beta ≤ eta := (radius_four_absorption r beta eta hr hbX heta1 hsX).2
  have htBase := hmem.1 x hxI
  have htD : (Tq dr Ar p q) x ∈ ParamRoom data.δ :=
    ⟨commonRoom_mono y0 ρ (min_le_left _ _) htBase.1,htBase.2⟩
  have htA : (Tq dr Ar p q) x ∈ ParamRoom D.dA :=
    ⟨commonRoom_mono y0 ρ (min_le_right _ _) htBase.1,htBase.2⟩
  have hSc := D.scalarCaps q hq dr hdr hdr1 Ar hAr p hp x hxClosed hbX
  have hGamma (i a b : Fin 3) :
      |ActualHigherSZeroCoefficientFactorisation.parameterConnection g L i a b ((Tq dr Ar p q) x)| ≤ D.Msc := by
    simpa only [ActualHigherSZeroCoefficientFactorisation.parameterConnection_eq g hg L,
      ActualHigherSZeroCoefficientFactorisation.parameterGramFrame,ActualHigherSFormation.higherSParam]
      using hSc.2.1 i a b
  have hc (z : ZeroWord) : |WC dr Ar p q x z| ≤ D.Msc^2*r :=
    abs_wordCoefficient_le_common r beta D.Msc _ _ _ hr hbX D.Msc_ge_one (hsX.trans heta1)
      hSc.1 hSc.2.2.1 hGamma z
  have hCoordX := D.coordinateBound q hq x hxClosed beta hbX F
  have hHigh := ActualLowerSSelfFormation.beta_mul_norm_higherSInput_sq_le_referenceProfileEnergy
    g L hg hO hD q beta hb0 F x
  let S : ℝ := ∑ k : Fin 3,‖du k‖^2
  have hInvS : beta⁻¹*S ≤ D.Cr*E := by
    have h0 : beta⁻¹*S ≤ coordinateEnergyDensity coordinateDirection beta (HU F) x := by
      unfold coordinateEnergyDensity
      change beta⁻¹*S ≤ beta⁻¹*S+beta*‖HU F x‖^2
      exact le_add_of_nonneg_right (by positivity)
    exact h0.trans hCoordX
  have hOne (k : Fin 3) : beta⁻¹*‖du k‖^2 ≤ D.Cr*E :=
    (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖du j‖) (Finset.mem_univ k)) (inv_nonneg.mpr hb0)).trans hInvS
  have hYoung (k : Fin 3) : ‖du k‖*‖UF F x‖ ≤ (1+D.Cr)*E :=
    (mul_le_weighted_sq beta ‖du k‖ ‖UF F x‖ hbpos).trans
      ((add_le_add (hOne k) hHigh).trans (le_of_eq (by ring)))
  have hRaw : |DR dr Ar p q F x| ≤ C0 D*eta*E :=
    actual_direct_point_of_caps
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D.atomRoom
      dr Ar p q F x htD htA D.Mf D.Cz D.Mop D.Msc D.Cr eta D.Mf_pos.le D.Cz_pos.le
      (zero_le_one.trans D.Mop_ge_one) (zero_le_one.trans D.Msc_ge_one) D.Cr_pos.le heta hbX
      (fun k => ⟨(hfc k).2.1.2.1,(hfc k).2.2.2.2.1⟩)
      ⟨hLin.2.2.1,hLin.2.2.2⟩ (D.atomCaps _ htA) (hLifts x) hc hYoung hHigh hr hr3 hr4
  have hC0CD := directCoefficientConstant_le_bound g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 D
  exact hRaw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0CD heta) hEX)
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
