import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualAllAngularAtomNativeBudgets
import Calderon.ActualAllAngularAtomScalarCaps

/-! Complete native ordinary-family caps through scalar-only finite aggregation.
No metric/data packet, low selection, final room constructor or cap premise. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomOrdinaryCaps
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

/-- Exact native slice interface; no finite-family order substitution. -/
private theorem high_atom_slice_budget {ι : Type}
    (F : Tpar → ι → Hi →L[ℝ] Half) (a : ι)
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (hSm : ContDiffOn ℝ ∞ (fun s => F s a) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M :=
  ActualAllAngularAtomNativeBudgets.exists_high_compact_jet_bound (fun s => F s a) S hK hS hSm N

/-- Exact native slice interface; no finite-family order substitution. -/
private theorem low_atom_slice_budget {ι : Type}
    (F : Tpar → ι → Half →L[ℝ] Neg) (a : ι)
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (hSm : ContDiffOn ℝ ∞ (fun s => F s a) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M :=
  ActualAllAngularAtomNativeBudgets.exists_low_compact_jet_bound (fun s => F s a) S hK hS hSm N

/-- Complete finite high-atom cap. The atom appears in exactly the original
curried order, and only scalar predicates enter the finite aggregation lemma. -/
theorem exists_high_atom_family_caps {ι : Type} [Fintype ι]
    (F : Tpar → ι → Hi →L[ℝ] Half)
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (hSm : ∀ a, ContDiffOn ℝ ∞ (fun s => F s a) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M := by
  let P : ι → ℝ → Prop := fun a M =>
    ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M
  have hMono : ∀ a x y, x ≤ y → P a x → P a y := by
    intro a x y hxy hx n hn t ht
    exact (hx n hn t ht).trans hxy
  have hSlice : ∀ a, ∃ M : ℝ, 0 ≤ M ∧ P a M := fun a =>
    high_atom_slice_budget F a S hK hS (hSm a) N
  exact ActualAllAngularAtomScalarCaps.exists_finite_monotone_cap P hMono hSlice

/-- Complete finite low-atom cap with the same native standard Sobolev norm. -/
theorem exists_low_atom_family_caps {ι : Type} [Fintype ι]
    (F : Tpar → ι → Half →L[ℝ] Neg)
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (hSm : ∀ a, ContDiffOn ℝ ∞ (fun s => F s a) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M := by
  let P : ι → ℝ → Prop := fun a M =>
    ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (fun s => F s a) S t‖ ≤ M
  have hMono : ∀ a x y, x ≤ y → P a x → P a y := by
    intro a x y hxy hx n hn t ht
    exact (hx n hn t ht).trans hxy
  have hSlice : ∀ a, ∃ M : ℝ, 0 ≤ M ∧ P a M := fun a =>
    low_atom_slice_budget F a S hK hS (hSm a) N
  exact ActualAllAngularAtomScalarCaps.exists_finite_monotone_cap P hMono hSlice

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomOrdinaryCaps
