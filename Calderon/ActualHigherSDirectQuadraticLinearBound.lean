import Calderon.ActualHigherSDirectWordPairGraphs
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

/-- Exact norm transport is performed before the pointwise ring normalization. -/
private lemma native_abs_pair_low_high_le (Low : Half →L[ℝ] Neg)
    (High : Hi →L[ℝ] Half) (z : Half) (U : Hi) (Z B A : ℝ)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ Z) (hLow : ‖Low‖ ≤ B) (hHigh : ‖High‖ ≤ A) :
    |QPP z (Low (High U))| ≤ ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Z*B*A*‖U‖ := by
  rw [ActualHigherSPairingNormDiagnostic.standardPairingNorm_eq_generic]
  exact abs_pair_low_high_le QPP Low High z U Z B A hZ hB hA hz hLow hHigh

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  ActualHigherSAdjointLeadingCoordinate.actualAdjointFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh sphereSobolevInclusionL sphereSobolevHalfToSphereL2L
  ActualHigherSFormation.higherSInput ActualHigherSScalarCommutatorNativeForm.halfInput
  atomHigh atomLow atomReverseHigh atomReverseLow

lemma actual_direct_quadratic_linear_of_caps {dA : ℝ} (P : ARoom dA)
    (dr Ar : ℝ) (p : ℕ) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (htA : (Tq dr Ar p q) x ∈ ParamRoom dA)
    (Cz Mop Msc eta : ℝ) (hCz : 0 ≤ Cz) (hMop : 0 ≤ Mop) (hMsc : 0 ≤ Msc)
    (heta : 0 ≤ eta) (hb : 1 ≤ actualReferenceBeta g L q dr Ar p x)
    (hLin : ‖ZH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x ∧
      ‖TH dr Ar p q x‖ ≤ Cz*(referenceRadius dr Ar p L x)^2*actualReferenceBeta g L q dr Ar p x)
    (hAtoms : ∀ a : ZeroAtom,‖AH ((Tq dr Ar p q) x) a‖ ≤ Mop ∧
      ‖AL ((Tq dr Ar p q) x) a‖ ≤ Mop ∧ ‖RH ((Tq dr Ar p q) x) a‖ ≤ Mop ∧
      ‖RL ((Tq dr Ar p q) x) a‖ ≤ Mop)
    (hLifts : (∀ a : ZeroAtom,IH (VA dr Ar p q F x a)=AH ((Tq dr Ar p q) x) a (UF F x)) ∧
      (∀ a : ZeroAtom,IH (VB dr Ar p q F x a)=RH ((Tq dr Ar p q) x) a (UF F x)))
    (hc : ∀ z : ZeroWord,|WC dr Ar p q x z| ≤ Msc^2*referenceRadius dr Ar p L x)
    (hHigh : actualReferenceBeta g L q dr Ar p x*‖UF F x‖^2 ≤
      finiteCoreReferenceProfileEnergy hO hD g hg L q (actualReferenceBeta g L q dr Ar p x) F x)
    (hr : 0 ≤ referenceRadius dr Ar p L x)
    (h3 : (referenceRadius dr Ar p L x)^3 ≤ eta) :
    |DQ dr Ar p q F x| ≤
      (828*ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP*Cz*Mop^2*Msc^2)*eta*
      finiteCoreReferenceProfileEnergy hO hD g hg L q
      (actualReferenceBeta g L q dr Ar p x) F x := by
  let r := referenceRadius dr Ar p L x
  let beta := actualReferenceBeta g L q dr Ar p x
  let U := UF F x
  let E := finiteCoreReferenceProfileEnergy hO hD g hg L q beta F x
  let z := ZH dr Ar p q x U
  let zR := TH dr Ar p q x U
  let du := fun k => directionalFDeriv (coordinateDirection k) (HU F) x
  let dU := fun k => directionalFDeriv (coordinateDirection k) (UF F) x
  let t := (Tq dr Ar p q) x
  let N := ActualHigherSPairingNormDiagnostic.standardPairingNorm QPP
  have hN : 0 ≤ N := ActualHigherSPairingNormDiagnostic.native_pairing_norm_nonneg
  have hb0 : 0 ≤ beta := zero_le_one.trans hb
  have hE : 0 ≤ E := finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L q beta hb0 F x
  have hz : ‖z‖ ≤ Cz*r^2*beta*‖U‖ := (ZH dr Ar p q x).le_opNorm U |>.trans
    (mul_le_mul_of_nonneg_right hLin.1 (norm_nonneg _))
  have hzR : ‖zR‖ ≤ Cz*r^2*beta*‖U‖ := (TH dr Ar p q x).le_opNorm U |>.trans
    (mul_le_mul_of_nonneg_right hLin.2 (norm_nonneg _))
  let first := fun w : ZeroWord => (wordAtoms w).1
  let second := fun w : ZeroWord => (wordAtoms w).2
  have hZ2 : ⟪KL (Z2 dr Ar p q F x),ZO dr Ar p q F x⟫_ℝ=
      ∑ w : ZeroWord,WC dr Ar p q x w*QPP z (AL t (first w) (AH t (second w) U)) := by
    exact actual_forward_word_pair_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 P dr Ar p q F x htA hLifts.1
  have hT2 : ⟪KL (T2 dr Ar p q F x),TO dr Ar p q F x⟫_ℝ=
      ∑ w : ZeroWord,WC dr Ar p q x w*QPP zR (RL t (second w) (RH t (first w) U)) := by
    exact actual_reverse_word_pair_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 P dr Ar p q F x htA hLifts.2
  have hSum : (∑ w : ZeroWord,|WC dr Ar p q x w|) ≤ 207*Msc^2*r := by
    calc
      _ ≤ ∑ _w : ZeroWord,Msc^2*r := Finset.sum_le_sum (fun w _ => hc w)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,card_zeroWord,nsmul_eq_mul]; norm_num <;> ring
  have hWordRow (Low : Half →L[ℝ] Neg) (High : Hi →L[ℝ] Half) (zz : Half)
      (hL : ‖Low‖ ≤ Mop) (hH : ‖High‖ ≤ Mop) (hZ : ‖zz‖ ≤ Cz*r^2*beta*‖U‖) :
      |QPP zz (Low (High U))| ≤ N*Cz*Mop^2*r^2*beta*‖U‖^2 := by
    have h : |QPP zz (Low (High U))| ≤ N*(Cz*r^2*beta*‖U‖)*Mop*Mop*‖U‖ :=
      native_abs_pair_low_high_le Low High zz U (Cz*r^2*beta*‖U‖) Mop Mop
        (by positivity) hMop hMop hZ hL hH
    exact h.trans (le_of_eq (by ring))
  have hQuadraticPair (A : ℝ) (f : ZeroWord → ℝ)
      (hEq : A=∑ w : ZeroWord,WC dr Ar p q x w*f w)
      (hf : ∀ w,|f w| ≤ N*Cz*Mop^2*r^2*beta*‖U‖^2) :
      |A| ≤ (207*N*Cz*Mop^2*Msc^2)*eta*E := by
    rw [hEq]
    calc
      _ ≤ (∑ w : ZeroWord,|WC dr Ar p q x w|)*(N*Cz*Mop^2*r^2*beta*‖U‖^2) :=
        abs_weighted_sum_le _ f _ (by positivity) hf
      _ ≤ (207*Msc^2*r)*(N*Cz*Mop^2*r^2*beta*‖U‖^2) := by gcongr
      _ = (207*N*Cz*Mop^2*Msc^2)*(r^3)*(beta*‖U‖^2) := by ring
      _ ≤ (207*N*Cz*Mop^2*Msc^2)*eta*E := by gcongr
  have hZQ := hQuadraticPair _ _ hZ2 (fun w =>
    hWordRow _ _ z (hAtoms (first w)).2.1 (hAtoms (second w)).1 hz)
  have hTQ := hQuadraticPair _ _ hT2 (fun w =>
    hWordRow _ _ zR (hAtoms (second w)).2.2.2 (hAtoms (first w)).2.2.1 hzR)
  have hQuad : |DQ dr Ar p q F x| ≤ (828*N*Cz*Mop^2*Msc^2)*eta*E := by
    unfold directQuadraticLinear
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hZQ hTQ))
      (by norm_num : (0 : ℝ)≤2)).trans (le_of_eq (by ring))
  exact hQuad

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectLower
