import Calderon.ActualHigherSDoubleQuarticIdentity
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualFixedAtomFiniteLifts
import Calderon.ActualSobolevDegreeGraphLifting
import Calderon.ActualHigherSAdjointFormation
import Calderon.ActualHigherSAdjointLeadingCoordinate

/-! Actual207-word specialization. No analytic bound is proved here. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuartic
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualFixedAtomFiniteLifts ActualRetainedGeneratorMultiplierGains
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

/-- Forward Hi lifts are built only on the original finite input. -/
def actualAtomHi (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ZeroAtom → Hi
  | Sum.inl i => VF dr Ar p q hreg data.δ0 data.germs F i x
  | Sum.inr (Sum.inl (Sum.inl ij)) => rotationFiniteHi hO hD F ij.1 ij.2 x
  | Sum.inr (Sum.inl (Sum.inr _)) =>
      finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F) x
  | Sum.inr (Sum.inr i) => raisingFiniteHi hF hO hD F i x

/-- Genuine reverse lifts: negative rotation, unchanged degree, canonical lowering. -/
def actualReverseAtomHi (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : ZeroAtom → Hi
  | Sum.inl i => VR hreg data.δ0 data.germs dr Ar p q F i x
  | Sum.inr (Sum.inl (Sum.inl ij)) => -rotationFiniteHi hO hD F ij.1 ij.2 x
  | Sum.inr (Sum.inl (Sum.inr _)) =>
      finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F) x
  | Sum.inr (Sum.inr i) => loweringFiniteHi hF hO hD F i x
local notation "VA" => actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "VB" => actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

/-- Full angular-order-two physical Half field, all207 ordered words. -/
def actualZ2Half (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  quadraticZeroHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 dr Ar p q x (VA dr Ar p q F x)
/-- Same coefficients, literal reversed genuine adjoint words. -/
def actualT2Half (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) : Half :=
  quadraticZeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    g2 dr Ar p q x (VB dr Ar p q F x)
local notation "Z2" => actualZ2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
local notation "T2" => actualT2Half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

def quarticWordRow {d : ℝ} (P : ARoom d) (t : Tpar) (U : Hi) (z v : ZeroWord) : ℝ :=
  let i := (wordAtoms z).1
  let j := (wordAtoms z).2
  let k := (wordAtoms v).1
  let l := (wordAtoms v).2
  PP (AH t j U) (P.gainLow i k t (AH t l U)) +
    PP (AH t j U) (AL t k (P.gainHigh i l t U)) +
    PP (P.gainHigh k j t U) (AL t l (RH t i U)) +
    PP (RH t k U) (P.gainLow j l t (RH t i U))
local notation "QR" => quarticWordRow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data

lemma actualAtomHi_inclusions (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) (x : R3) :
    (∀ a : ZeroAtom, IH (VA dr Ar p q F x a) = AH ((Tq dr Ar p q) x) a (UF F x)) ∧
    (∀ a : ZeroAtom, IH (VB dr Ar p q F x a) = RH ((Tq dr Ar p q) x) a (UF F x)) := by
  have hE (j : Fin 3) := ActualCommonFirstWordQuadraticAdjoint.fwdLift_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs dF Cm dr Ar p hdr hAr q F hT j x
  have hB (i : Fin 3) := ActualReverseEHigherLift.reverseEHigherLift_inclusion
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg data.δ0 data.germs dF Cm.rev dr Ar p q F hT i x
  constructor
  · intro a
    cases a with
    | inl i => simpa only [actualAtomHi, atomHigh] using hE i
    | inr a =>
      cases a with
      | inl V =>
        cases V with
        | inl ij => simpa only [actualAtomHi, atomHigh, generatorHigh, ActualHigherSFormation.higherSInput] using
            rotationFiniteHi_inclusion hO hD F ij.1 ij.2 x
        | inr z => simpa only [actualAtomHi, atomHigh, generatorHigh, ActualHigherSFormation.higherSInput] using
            DegreeGraphLifting.inclusion_finiteCoreSobolevLift_coreDegree hO hD F x
      | inr i => simpa only [actualAtomHi, atomHigh, ActualHigherSFormation.higherSInput] using
          raisingFiniteHi_inclusion hF hO hD F i x
  · intro a
    cases a with
    | inl i => simpa only [actualReverseAtomHi, atomReverseHigh,
        ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered] using hB i
    | inr a =>
      cases a with
      | inl V =>
        cases V with
        | inl ij => simpa only [actualReverseAtomHi, atomReverseHigh, ActualGeneratorEPairedGainedEndpoints.generatorSharpHigh,
            generatorHigh, ContinuousLinearMap.neg_apply, map_neg, ActualHigherSFormation.higherSInput] using
            congrArg (fun v : Half => -v) (rotationFiniteHi_inclusion hO hD F ij.1 ij.2 x)
        | inr z => simpa only [actualReverseAtomHi, atomReverseHigh, ActualGeneratorEPairedGainedEndpoints.generatorSharpHigh,
            generatorHigh, ActualHigherSFormation.higherSInput] using
            DegreeGraphLifting.inclusion_finiteCoreSobolevLift_coreDegree hO hD F x
      | inr i => simpa only [actualReverseAtomHi, atomReverseHigh, ActualHigherSFormation.higherSInput] using
          loweringFiniteHi_inclusion hF hO hD F i x

/-- Exact whole forward word sum, without expanding the concrete word index. -/
lemma actualZ2Half_eq_sum (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Z2 g2 dr Ar p q F x =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        AH ((Tq dr Ar p q) x) (wordAtoms z).1 (VA dr Ar p q F x (wordAtoms z).2) := by
  rfl

/-- Exact whole genuine reverse sum; both word order and partner stay literal. -/
lemma actualT2Half_eq_sum (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    T2 g2 dr Ar p q F x =
      ∑ z : ZeroWord, WC g2 dr Ar p q x z •
        RH ((Tq dr Ar p q) x) (wordAtoms z).2 (VB dr Ar p q F x (wordAtoms z).1) := by
  rfl

/-- Zero original forward lifts give a zero physical forward sum pointwise. -/
lemma actualZ2Half_eq_zero_of_lifts_eq_zero
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hV : ∀ b : ZeroAtom, VA dr Ar p q F x b = 0) :
    Z2 g2 dr Ar p q F x = 0 := by
  rw [actualZ2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x]
  apply Finset.sum_eq_zero
  intro z _
  rw [hV (wordAtoms z).2, map_zero, smul_zero]

/-- Zero original genuine reverse lifts give a zero reverse sum pointwise. -/
lemma actualT2Half_eq_zero_of_lifts_eq_zero
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hv : ∀ b : ZeroAtom, VB dr Ar p q F x b = 0) :
    T2 g2 dr Ar p q F x = 0 := by
  rw [actualT2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x]
  apply Finset.sum_eq_zero
  intro z _
  rw [hv (wordAtoms z).1, map_zero, smul_zero]

/-- The original two lift families vanish off the original input support. -/
lemma actualAtomHi_eq_zero_off_support (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ y ∈ tsupport F.val, (Tq dr Ar p q) y ∈ ParamRoom dF)
    (x : R3) (hx : x ∉ tsupport F.val) :
    (∀ b : ZeroAtom, VA dr Ar p q F x b = 0) ∧
      (∀ b : ZeroAtom, VB dr Ar p q F x b = 0) := by
  have hLifts := actualAtomHi_inclusions g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hT x
  have hU0 : UF F x = 0 := ActualHigherSFormation.higherSInput_eq_zero
    hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q F x hx
  have hI : Function.Injective (IH : Hi →L[ℝ] Half) :=
    sphereSobolevInclusionL_injective (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  constructor
  · intro b
    apply hI
    calc
      IH (VA dr Ar p q F x b) = AH ((Tq dr Ar p q) x) b (UF F x) := hLifts.1 b
      _ = AH ((Tq dr Ar p q) x) b 0 := congrArg (AH ((Tq dr Ar p q) x) b) hU0
      _ = 0 := map_zero _
      _ = IH (0 : Hi) := (map_zero (IH : Hi →L[ℝ] Half)).symm
  · intro b
    apply hI
    calc
      IH (VB dr Ar p q F x b) = RH ((Tq dr Ar p q) x) b (UF F x) := hLifts.2 b
      _ = RH ((Tq dr Ar p q) x) b 0 := congrArg (RH ((Tq dr Ar p q) x) b) hU0
      _ = 0 := map_zero _
      _ = IH (0 : Hi) := (map_zero (IH : Hi →L[ℝ] Half)).symm

/-- Every original gained quartic row is zero at zero original input. -/
lemma quarticWordRow_zero {d : ℝ} (P : ARoom d) (t : Tpar) (z v : ZeroWord) :
    QR P t (0 : Hi) z v = 0 := by
  simp only [quarticWordRow, map_zero, halfPairing_zero_left, add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuartic
