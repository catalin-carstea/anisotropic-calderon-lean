import Calderon.ActualHigherSActualCubicPairing
import Calderon.ActualHigherSMixedCubicWordPairings
import Calderon.ActualHigherSQuadraticZeroNegativePointGraphs

/-! Literal full3*3*207 mixed physical contraction, author source uncompiled.
Canonical own4511 first fields keep the original reverse minus. Every word and
coefficient order is retained. No output angular restriction or analytic callback. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicPhysicalExpansion
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
  ActualHigherSQuadraticZeroQuartic ActualHigherSActualCubicPairing PrincipalCommutator
  ReferenceDensityBounds ActualHigherSLeadingBracketGain
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

local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "PF" => ActualPPLowerRemainder.actualPPFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PR" => ActualPPLowerRemainder.actualPPReverseFirstOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PH" => ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "DH" => ActualPPLowerRemainder.actualPPReverseFirstHigh
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "MD" => actualMixedCubicDensity
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow sphereSobolevInclusionL
  ActualHigherSFirstPhysicalCommutatorGraph.highFirstCoordinateCoefficient
  ActualPPLowerRemainder.actualPPReverseFirstHigh actualZ2Half actualT2Half cubicAtomForm

lemma actual_mixed_cubic_two_pairings_at {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ =
      (∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (AH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (AL ((Tq dr Ar p q) x) (wordAtoms z).1
              (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))) ∧
    ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ =
      -(∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (RH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (RL ((Tq dr Ar p q) x) (wordAtoms z).2
              (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))) := by
  exact actual_first_pairings_eq_word_sums
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x
    (Z2 g2 dr Ar p q F x) (T2 g2 dr Ar p q F x)
    (ActualHigherSQuadraticZeroNegativeGraphs.actualZ2Half_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P dF Cm g2 dr Ar p hdr hAr q F hTF x ht)
    (ActualHigherSQuadraticZeroNegativeGraphs.actualT2Half_negative_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P dF Cm g2 dr Ar p hdr hAr q F hTF x ht)

lemma actual_mixed_cubic_finite_sum_at {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (x : R3) (ht : (Tq dr Ar p q) x ∈ ParamRoom d) :
    MD g2 dr Ar p q F x =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x)
            (eAtom i) (wordAtoms z).1 (wordAtoms z).2
            (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x) := by
  have hPair := actual_mixed_cubic_two_pairings_at
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    P dF Cm g2 dr Ar p hdr hAr q F hTF x ht
  have hSub := congrArg₂ (fun a b : ℝ => a-b) hPair.1 hPair.2
  simpa only [actualMixedCubicDensity, cubicAtomForm_apply, mul_add,
    Finset.sum_add_distrib, sub_neg_eq_add] using hSub

lemma actual_mixed_cubic_finite_sum {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (hTP : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom d) (x : R3) :
    MD g2 dr Ar p q F x =
      ∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          cubicAtomForm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 ((Tq dr Ar p q) x)
            (eAtom i) (wordAtoms z).1 (wordAtoms z).2
            (directionalFDeriv (coordinateDirection k) (UF F) x) (UF F x) := by
  by_cases hx : x ∈ tsupport F.val
  · exact actual_mixed_cubic_finite_sum_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P dF Cm g2 dr Ar p hdr hAr q F hTF x (hTP x hx)
  · have h0 := ActualHigherSQuadraticZeroNegativeGraphs.actualZ2T2_eq_zero_off_input_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      dF Cm g2 dr Ar p hdr hAr q F hTF x hx
    have hU0 := ActualHigherSFormation.higherSInput_eq_zero
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hx
    simp only [actualMixedCubicDensity, h0.1, h0.2, map_zero, inner_zero_right,
      sub_self, hU0, mul_zero, Finset.sum_const_zero]

lemma actual_mixed_cubic_two_pairings {d : ℝ} (P : ARoom d) (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF)
    (hTP : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom d) (x : R3) :
    ⟪PF g2 dr Ar p q F x, KL (Z2 g2 dr Ar p q F x)⟫_ℝ =
      (∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (AH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (AL ((Tq dr Ar p q) x) (wordAtoms z).1
              (AH ((Tq dr Ar p q) x) (wordAtoms z).2 (UF F x)))) ∧
    ⟪PR g2 dr Ar p q F x, KL (T2 g2 dr Ar p q F x)⟫_ℝ =
      -(∑ k : Fin 3, ∑ i : Fin 3, ∑ z : ZeroWord,
        mixedWordScalar g L g2 dr Ar p q k i z x *
          PP (RH ((Tq dr Ar p q) x) (eAtom i)
            (directionalFDeriv (coordinateDirection k) (UF F) x))
            (RL ((Tq dr Ar p q) x) (wordAtoms z).2
              (RH ((Tq dr Ar p q) x) (wordAtoms z).1 (UF F x)))) := by
  by_cases hx : x ∈ tsupport F.val
  · exact actual_mixed_cubic_two_pairings_at
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      P dF Cm g2 dr Ar p hdr hAr q F hTF x (hTP x hx)
  · have h0 := ActualHigherSQuadraticZeroNegativeGraphs.actualZ2T2_eq_zero_off_input_support
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
      dF Cm g2 dr Ar p hdr hAr q F hTF x hx
    have hU0 := ActualHigherSFormation.higherSInput_eq_zero
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hx
    simp only [h0.1, h0.2, hU0, map_zero, sphereSobolevDualPairing,
      inner_zero_right, mul_zero, Finset.sum_const_zero, neg_zero, and_self]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSMixedCubicPhysicalExpansion
