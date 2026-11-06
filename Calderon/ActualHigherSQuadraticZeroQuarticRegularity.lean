import Calderon.ActualHigherSQuadraticZeroQuartic
import Calderon.ActualHigherSQuarticBound
import Calderon.ActualHigherSLinearZeroScalarCaps
import Calderon.ActualLowerSSelfFormation
import Calderon.ActualHigherSIntegratedPairing
import Calderon.FixedParameterProfilePullback
import Calderon.ActualHigherSZeroWordCoefficientRegularity
import Calderon.ActualHigherSZeroWordCoefficientProfileRegularity

/-! Complete actual 207-word quartic uniform estimate.
No analytic callback escapes the final theorem. -/
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

section CoefficientRegularity
include hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 Room hreg data

lemma contDiff_actualWordCoefficient (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (z : ZeroWord) :
    ContDiff ℝ ∞ (fun x : R3 => WC g2 dr Ar p q x z) := by
  exact contDiff_actualWordCoefficient_scalar g g2 hg hg2 L dr Ar p hdr hAr q z

end CoefficientRegularity

lemma contDiff_actualAtomHi (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) (b : ZeroAtom) :
    ContDiff ℝ ∞ (fun x => VA dr Ar p q F x b) := by
  cases b with
  | inl i =>
    simpa only [actualAtomHi] using
      ActualCommonFirstWordQuadraticAdjoint.contDiff_fwdLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg data.δ0 data.germs dF Cm dr Ar p hdr hAr q F hT i
  | inr b =>
    cases b with
    | inl V =>
      cases V with
      | inl ij =>
        simpa only [actualAtomHi] using
          (fixed_finite_lifts_contDiff hF hO hD F ij.1 ij.2).1
      | inr z =>
        simpa only [actualAtomHi] using
          contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F)
    | inr i =>
      simpa only [actualAtomHi] using
        (fixed_finite_lifts_contDiff hF hO hD F i 0).2.1

lemma contDiff_actualReverseAtomHi (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) (b : ZeroAtom) :
    ContDiff ℝ ∞ (fun x => VB dr Ar p q F x b) := by
  cases b with
  | inl i =>
    simpa only [actualReverseAtomHi] using
      ActualReverseEHigherLift.contDiff_reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg data.δ0 data.germs dF Cm.rev dr Ar p hdr hAr q F hT i
  | inr b =>
    cases b with
    | inl V =>
      cases V with
      | inl ij =>
        simpa only [actualReverseAtomHi] using
          ((fixed_finite_lifts_contDiff hF hO hD F ij.1 ij.2).1).neg
      | inr z =>
        simpa only [actualReverseAtomHi] using
          contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) (coreDegree hO hD F)
    | inr i =>
      simpa only [actualReverseAtomHi] using
        (fixed_finite_lifts_contDiff hF hO hD F i 0).2.2

lemma actualAtomHi_contDiff_and_zero (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    (∀ a : ZeroAtom, ContDiff ℝ ∞ (fun x => VA dr Ar p q F x a) ∧
      ∀ x ∉ tsupport F.val, VA dr Ar p q F x a = 0) ∧
    (∀ a : ZeroAtom, ContDiff ℝ ∞ (fun x => VB dr Ar p q F x a) ∧
      ∀ x ∉ tsupport F.val, VB dr Ar p q F x a = 0) := by
  constructor
  · intro b
    exact ⟨contDiff_actualAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data dF Cm dr Ar p hdr hAr q F hT b,
      fun x hx => (actualAtomHi_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data dF Cm dr Ar p hdr hAr q F hT x hx).1 b⟩
  · intro b
    exact ⟨contDiff_actualReverseAtomHi g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data dF Cm dr Ar p hdr hAr q F hT b,
      fun x hx => (actualAtomHi_eq_zero_off_support g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data dF Cm dr Ar p hdr hAr q F hT x hx).2 b⟩

lemma atomReverseHigh_e_family_eq (i : Fin 3) :
    (fun t : Tpar => RH t (Sum.inl i)) =
      ActualGeneratorEPairedGainedEndpoints.reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i := by
  funext t
  simp only [atomReverseHigh, ActualHigherSAdjointLeadingCoordinate.reverseEHigh_eq_ordered]

lemma actualZ2T2_contDiff_support (dF : ℝ)
    (Cm : ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg data.δ0 data.germs dF)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (dr Ar : ℝ) (p : ℕ)
    (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ x ∈ tsupport F.val, (Tq dr Ar p q) x ∈ ParamRoom dF) :
    ContDiff ℝ ∞ (Z2 g2 dr Ar p q F) ∧ ContDiff ℝ ∞ (T2 g2 dr Ar p q F) ∧
      tsupport (Z2 g2 dr Ar p q F) ⊆ tsupport F.val ∧
      tsupport (T2 g2 dr Ar p q F) ⊆ tsupport F.val := by
  have hL := actualAtomHi_contDiff_and_zero
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data
    dF Cm dr Ar p hdr hAr q F hT
  have hA (a : ZeroAtom) : ∀ x ∈ tsupport F.val, ContDiffAt ℝ ∞ (fun t => AH t a) ((Tq dr Ar p q) x) := by
    intro x hx
    cases a with
    | inl i => exact Cm.germHigh i _ (hT x hx)
    | inr a => cases a <;> exact contDiffAt_const
  have hB (a : ZeroAtom) : ∀ x ∈ tsupport F.val, ContDiffAt ℝ ∞ (fun t => RH t a) ((Tq dr Ar p q) x) := by
    intro x hx
    cases a with
    | inl i =>
      rw [atomReverseHigh_e_family_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i]
      exact Cm.rev.germHigh i _ (hT x hx)
    | inr a => cases a <;> exact contDiffAt_const
  have hFWord (z : ZeroWord) : ContDiff ℝ ∞
      (fun x => AH ((Tq dr Ar p q) x) (wordAtoms z).1 (VA dr Ar p q F x (wordAtoms z).2)) :=
    ActualHigherSFormation.contDiff_family_apply
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q
      (fun t => AH t (wordAtoms z).1) F (hA _) (fun x => VA dr Ar p q F x (wordAtoms z).2)
      (hL.1 _).1 (hL.1 _).2
  have hRWord (z : ZeroWord) : ContDiff ℝ ∞
      (fun x => RH ((Tq dr Ar p q) x) (wordAtoms z).2 (VB dr Ar p q F x (wordAtoms z).1)) :=
    ActualHigherSFormation.contDiff_family_apply
      hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 dr Ar p hdr hAr q
      (fun t => RH t (wordAtoms z).2) F (hB _) (fun x => VB dr Ar p q F x (wordAtoms z).1)
      (hL.2 _).1 (hL.2 _).2
  have hFSum : ContDiff ℝ ∞ (fun x : R3 => ∑ z : ZeroWord,
      WC g2 dr Ar p q x z • AH ((Tq dr Ar p q) x) (wordAtoms z).1
        (VA dr Ar p q F x (wordAtoms z).2)) :=
    ContDiff.sum (s := Finset.univ) (fun z _ => (contDiff_actualWordCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q z).smul (hFWord z))
  have hRSum : ContDiff ℝ ∞ (fun x : R3 => ∑ z : ZeroWord,
      WC g2 dr Ar p q x z • RH ((Tq dr Ar p q) x) (wordAtoms z).2
        (VB dr Ar p q F x (wordAtoms z).1)) :=
    ContDiff.sum (s := Finset.univ) (fun z _ => (contDiff_actualWordCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 hg2 dr Ar p hdr hAr q z).smul (hRWord z))
  have hEqZ : Z2 g2 dr Ar p q F = (fun x : R3 => ∑ z : ZeroWord,
      WC g2 dr Ar p q x z • AH ((Tq dr Ar p q) x) (wordAtoms z).1
        (VA dr Ar p q F x (wordAtoms z).2)) :=
    funext (fun x => actualZ2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)
  have hEqT : T2 g2 dr Ar p q F = (fun x : R3 => ∑ z : ZeroWord,
      WC g2 dr Ar p q x z • RH ((Tq dr Ar p q) x) (wordAtoms z).2
        (VB dr Ar p q F x (wordAtoms z).1)) :=
    funext (fun x => actualT2Half_eq_sum g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x)
  have hFS : ContDiff ℝ ∞ (Z2 g2 dr Ar p q F) := hEqZ.symm ▸ hFSum
  have hRS : ContDiff ℝ ∞ (T2 g2 dr Ar p q F) := hEqT.symm ▸ hRSum
  have hFSupport : Function.support (Z2 g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hn
    apply hx
    have hV0 (a : ZeroAtom) : VA dr Ar p q F x a = 0 := (hL.1 a).2 x hn
    exact actualZ2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hV0
  have hRSupport : Function.support (T2 g2 dr Ar p q F) ⊆ tsupport F.val := by
    intro x hx
    by_contra hn
    apply hx
    have hv0 (a : ZeroAtom) : VB dr Ar p q F x a = 0 := (hL.2 a).2 x hn
    exact actualT2Half_eq_zero_of_lifts_eq_zero g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data g2 dr Ar p q F x hv0
  exact ⟨hFS, hRS, closure_minimal hFSupport (isClosed_tsupport _),
    closure_minimal hRSupport (isClosed_tsupport _)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuadraticZeroQuarticBounds
