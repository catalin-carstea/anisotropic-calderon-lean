import Calderon.ActualHigherSDoubleQuarticIdentity
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualFixedAtomFiniteLifts
import Calderon.ActualSobolevDegreeGraphLifting
import Calderon.ActualHigherSAdjointFormation
import Calderon.ActualHigherSAdjointLeadingCoordinate

/-! Exact pointwise dictionary identification at native CLM types. These
complete branch proofs diagnose conversion without changing any atom or norm. -/
set_option autoImplicit false
set_option pp.all true
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroAtomDictionary
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

/-- Literal equality of the two existing atomHigh dictionaries, branch by branch. -/
lemma atomHigh_eq_angularAtomHigh (t : Tpar) (b : ZeroAtom) :
    ActualHigherSQuadraticZeroWords.atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b =
      ActualAllAngularAtomGainedRoom.angularAtomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b := by
  cases b with
  | inl i => rfl
  | inr b =>
    cases b with
    | inl V => rfl
    | inr i => rfl

/-- Literal equality of the two existing atomLow dictionaries, branch by branch. -/
lemma atomLow_eq_angularAtomLow (t : Tpar) (b : ZeroAtom) :
    ActualHigherSQuadraticZeroWords.atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b =
      ActualAllAngularAtomGainedRoom.angularAtomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b := by
  cases b with
  | inl i => rfl
  | inr b =>
    cases b with
    | inl V => rfl
    | inr i => rfl

/-- Literal equality of the two existing atomReverseHigh dictionaries, branch by branch. -/
lemma atomReverseHigh_eq_angularAtomReverseHigh (t : Tpar) (b : ZeroAtom) :
    ActualHigherSQuadraticZeroWords.atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b =
      ActualAllAngularAtomGainedRoom.angularAtomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b := by
  cases b with
  | inl i => rfl
  | inr b =>
    cases b with
    | inl V => rfl
    | inr i => rfl

/-- Literal equality of the two existing atomReverseLow dictionaries, branch by branch. -/
lemma atomReverseLow_eq_angularAtomReverseLow (t : Tpar) (b : ZeroAtom) :
    ActualHigherSQuadraticZeroWords.atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b =
      ActualAllAngularAtomGainedRoom.angularAtomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t b := by
  cases b with
  | inl i => rfl
  | inr b =>
    cases b with
    | inl V => rfl
    | inr i => rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSZeroAtomDictionary
