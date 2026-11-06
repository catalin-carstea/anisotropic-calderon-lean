import Calderon.ActualAllAngularAtomGainedRoom
import Calderon.ActualHigherSQuadraticZeroWords
import Calderon.ActualHigherSZeroAtomDictionary

/-! Native Word-family first caps, independent of physical profile assembly.
One actual Room cap M precedes all atoms and parameter points. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAllAtomNativeCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ConformalDepth
  ActualHigherSQuadraticZeroWords ActualRetainedGeneratorMultiplierGains
  ReferenceWeightedApproximation
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
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

local notation "AH" => atomHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "AL" => atomLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RH" => atomReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RL" => atomReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ARoom" d:max => ActualAllAngularAtomGainedRoom.AllAngularAtomRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg data d
local notation "WC" => actualWordCoefficient g L


-- These generic equality eliminations do not normalize native operator bodies.
lemma contDiffOn_of_function_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f f' : Tpar → V} (heq : f = f') {S : Set Tpar}
    (h : ContDiffOn ℝ ∞ f' S) : ContDiffOn ℝ ∞ f S := by
  cases heq
  exact h

lemma first_within_caps_of_function_eq {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f f' : Tpar → V} (heq : f = f') (S : Set Tpar) (M : ℝ)
    (h : ∀ n : ℕ, n ≤ 1 → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n f' S t‖ ≤ M) :
    ∀ n : ℕ, n ≤ 1 → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n f S t‖ ≤ M := by
  cases heq
  exact h

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  atomHigh atomLow atomReverseHigh atomReverseLow sphereSobolevInclusionL
  ActualAllAngularAtomGainedRoom.angularAtomHigh ActualAllAngularAtomGainedRoom.angularAtomLow
  ActualAllAngularAtomGainedRoom.angularAtomReverseHigh ActualAllAngularAtomGainedRoom.angularAtomReverseLow

lemma atomHigh_family_eq_angular (aa : ZeroAtom) :
    (fun t : Tpar => AH t aa) =
      (fun t : Tpar => ActualAllAngularAtomGainedRoom.angularAtomHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa) := by
  funext t
  exact ActualHigherSZeroAtomDictionary.atomHigh_eq_angularAtomHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa

lemma atomLow_family_eq_angular (aa : ZeroAtom) :
    (fun t : Tpar => AL t aa) =
      (fun t : Tpar => ActualAllAngularAtomGainedRoom.angularAtomLow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa) := by
  funext t
  exact ActualHigherSZeroAtomDictionary.atomLow_eq_angularAtomLow
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa

lemma atomReverseHigh_family_eq_angular (aa : ZeroAtom) :
    (fun t : Tpar => RH t aa) =
      (fun t : Tpar => ActualAllAngularAtomGainedRoom.angularAtomReverseHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa) := by
  funext t
  exact ActualHigherSZeroAtomDictionary.atomReverseHigh_eq_angularAtomReverseHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa

lemma atomReverseLow_family_eq_angular (aa : ZeroAtom) :
    (fun t : Tpar => RL t aa) =
      (fun t : Tpar => ActualAllAngularAtomGainedRoom.angularAtomReverseLow
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa) := by
  funext t
  exact ActualHigherSZeroAtomDictionary.atomReverseLow_eq_angularAtomReverseLow
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t aa

structure ActualAtomNativeFirstCaps (d M : ℝ) : Prop where
  highSmooth : ∀ aa : ZeroAtom, ContDiffOn ℝ ∞ (fun t => AH t aa) (ParamRoom d)
  lowSmooth : ∀ aa : ZeroAtom, ContDiffOn ℝ ∞ (fun t => AL t aa) (ParamRoom d)
  reverseHighSmooth : ∀ aa : ZeroAtom, ContDiffOn ℝ ∞ (fun t => RH t aa) (ParamRoom d)
  reverseLowSmooth : ∀ aa : ZeroAtom, ContDiffOn ℝ ∞ (fun t => RL t aa) (ParamRoom d)
  highJetBound : ∀ aa : ZeroAtom, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom d,
    ‖iteratedFDerivWithin ℝ n (fun s => AH s aa) (ParamRoom d) t‖ ≤ M
  lowJetBound : ∀ aa : ZeroAtom, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom d,
    ‖iteratedFDerivWithin ℝ n (fun s => AL s aa) (ParamRoom d) t‖ ≤ M
  reverseHighJetBound : ∀ aa : ZeroAtom, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom d,
    ‖iteratedFDerivWithin ℝ n (fun s => RH s aa) (ParamRoom d) t‖ ≤ M
  reverseLowJetBound : ∀ aa : ZeroAtom, ∀ n : ℕ, n ≤ 1 → ∀ t ∈ ParamRoom d,
    ‖iteratedFDerivWithin ℝ n (fun s => RL s aa) (ParamRoom d) t‖ ≤ M

local notation "NativeCaps" => ActualAtomNativeFirstCaps
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The same Room's one common first-jet cap, transported to all actual Word families. -/
theorem exists_actual_allAtom_native_first_caps {d : ℝ} (P : ARoom d) :
    ∃ M : ℝ, 1 ≤ M ∧ NativeCaps d M := by
  obtain ⟨M, hM, hAtom, _hGain⟩ := P.finiteCaps 1
  refine ⟨M, hM, {
    highSmooth := ?_
    lowSmooth := ?_
    reverseHighSmooth := ?_
    reverseLowSmooth := ?_
    highJetBound := ?_
    lowJetBound := ?_
    reverseHighJetBound := ?_
    reverseLowJetBound := ?_ }⟩
  · intro aa
    exact contDiffOn_of_function_eq (atomHigh_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (P.atomSmooth aa).1
  · intro aa
    exact contDiffOn_of_function_eq (atomLow_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (P.atomSmooth aa).2.1
  · intro aa
    exact contDiffOn_of_function_eq (atomReverseHigh_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (P.atomSmooth aa).2.2.1
  · intro aa
    exact contDiffOn_of_function_eq (atomReverseLow_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (P.atomSmooth aa).2.2.2
  · intro aa
    exact first_within_caps_of_function_eq (atomHigh_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (ParamRoom d) M
      (fun n hn t ht => (hAtom aa n hn t ht).1)
  · intro aa
    exact first_within_caps_of_function_eq (atomLow_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (ParamRoom d) M
      (fun n hn t ht => (hAtom aa n hn t ht).2.1)
  · intro aa
    exact first_within_caps_of_function_eq (atomReverseHigh_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (ParamRoom d) M
      (fun n hn t ht => (hAtom aa n hn t ht).2.2.1)
  · intro aa
    exact first_within_caps_of_function_eq (atomReverseLow_family_eq_angular
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 aa) (ParamRoom d) M
      (fun n hn t ht => (hAtom aa n hn t ht).2.2.2)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSAllAtomNativeCaps
