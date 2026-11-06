import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualAllAngularAtomNativeBudgets
import Calderon.ActualAllAngularAtomOrdinaryCaps
import Calderon.ActualAllAngularAtomOrdinaryPairCaps
import Calderon.ActualAllAngularAtomRealSixCaps

/-! Complete six-family allN cap assembly on opaque actual endpoint types.
No metric/data packet, low selection, final room constructor or cap premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomFiniteCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly ActualJacobiAngularGainedRows
  ActualPiJacobiRadialGainedRows ActualRetainedGeneratorMultiplierGains
  ActualGeneratorEPairedGainedEndpoints ActualCanonicalGeneratorAngularGainedRows
  ActualCanonicalAngularGainedBracket NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Complete ordinary-four/gained-two finite jet caps from C∞ on one compact
room. All hypotheses are original structural smoothness facts, not cap budgets. -/
theorem exists_allN_atom_and_gain_caps {ι : Type} [Fintype ι]
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (AHi BHi : Tpar → ι → Hi →L[ℝ] Half)
    (ALo BLo : Tpar → ι → Half →L[ℝ] Neg)
    (GHi : ι → ι → Tpar → Hi →L[ℝ] Half)
    (GLo : ι → ι → Tpar → Half →L[ℝ] Neg)
    (hAtom : ∀ a : ι,
      ContDiffOn ℝ ∞ (fun t => AHi t a) S ∧
      ContDiffOn ℝ ∞ (fun t => ALo t a) S ∧
      ContDiffOn ℝ ∞ (fun t => BHi t a) S ∧
      ContDiffOn ℝ ∞ (fun t => BLo t a) S)
    (hHigh : ∀ a b, ContDiffOn ℝ ∞ (GHi a b) S)
    (hLow : ∀ a b, ContDiffOn ℝ ∞ (GLo a b) S) :
    ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧
      (∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
        ‖iteratedFDerivWithin ℝ n (fun s => AHi s a) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (fun s => ALo s a) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (fun s => BHi s a) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (fun s => BLo s a) S t‖ ≤ M) ∧
      (∀ a b : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
        ‖iteratedFDerivWithin ℝ n (GHi a b) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (GLo a b) S t‖ ≤ M) := by
  intro N
  exact @ActualAllAngularAtomRealSixCaps.exists_six_real_caps ι Tpar
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => AHi s a) S t‖)
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => BHi s a) S t‖)
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => ALo s a) S t‖)
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => BLo s a) S t‖)
    (fun a b n t => ‖iteratedFDerivWithin ℝ n (GHi a b) S t‖)
    (fun a b n t => ‖iteratedFDerivWithin ℝ n (GLo a b) S t‖)
    S N
    (@ActualAllAngularAtomOrdinaryPairCaps.exists_high_low_atom_family_caps
      ι (inferInstance : Fintype ι) S hK hS AHi ALo
      (fun a => (hAtom a).1) (fun a => (hAtom a).2.1) N)
    (@ActualAllAngularAtomOrdinaryPairCaps.exists_high_low_atom_family_caps
      ι (inferInstance : Fintype ι) S hK hS BHi BLo
      (fun a => (hAtom a).2.2.1) (fun a => (hAtom a).2.2.2) N)
    (@ActualAllAngularAtomNativeBudgets.exists_paired_high_low_jet_caps
      ι (inferInstance : Fintype ι) S hK hS GHi GLo hHigh hLow N)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomFiniteCaps
