import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket

/-! Concrete standard Sobolev-CLM compact jet budgets. No generic codomain
adapter, structure rewrite, actual packet or low-family choice context. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomNativeBudgets
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

/-- Monomorphic native compact jet bound with the original standard norm. -/
theorem exists_high_compact_jet_bound
    (f : Tpar → Hi →L[ℝ] Half) (S : Set Tpar) (hK : IsCompact S)
    (hUnique : UniqueDiffOn ℝ S) (hSm : ContDiffOn ℝ ∞ f S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n f S t‖ ≤ M :=
  exists_compact_iteratedFDerivWithin_bound f S hK hUnique hSm N

/-- Monomorphic native compact jet bound with the original standard norm. -/
theorem exists_low_compact_jet_bound
    (f : Tpar → Half →L[ℝ] Neg) (S : Set Tpar) (hK : IsCompact S)
    (hUnique : UniqueDiffOn ℝ S) (hSm : ContDiffOn ℝ ∞ f S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n f S t‖ ≤ M :=
  exists_compact_iteratedFDerivWithin_bound f S hK hUnique hSm N

/-- Concrete endpoint finite-family bound, proved directly by a finite sum
of native single-family bounds, with no abstract-codomain conversion. -/
theorem exists_finite_high_family_budget {ι : Type} [Fintype ι]
    (f : ι → Tpar → Hi →L[ℝ] Half) (S : Set Tpar)
    (hK : IsCompact S) (hUnique : UniqueDiffOn ℝ S)
    (hSm : ∀ i, ContDiffOn ℝ ∞ (f i) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (f i) S t‖ ≤ M := by
  classical
  choose Mi hMi using fun i : ι => exists_high_compact_jet_bound (f i) S hK hUnique (hSm i) N
  let M := ∑ i : ι, Mi i
  refine ⟨M,Finset.sum_nonneg (fun i _ => (hMi i).1),?_⟩
  intro i n hn t ht
  have hOne : Mi i ≤ M := Finset.single_le_sum
    (fun j _ => (hMi j).1) (Finset.mem_univ i)
  exact ((hMi i).2 n hn t ht).trans hOne

/-- Concrete endpoint finite-family bound, proved directly by a finite sum
of native single-family bounds, with no abstract-codomain conversion. -/
theorem exists_finite_low_family_budget {ι : Type} [Fintype ι]
    (f : ι → Tpar → Half →L[ℝ] Neg) (S : Set Tpar)
    (hK : IsCompact S) (hUnique : UniqueDiffOn ℝ S)
    (hSm : ∀ i, ContDiffOn ℝ ∞ (f i) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      ‖iteratedFDerivWithin ℝ n (f i) S t‖ ≤ M := by
  classical
  choose Mi hMi using fun i : ι => exists_low_compact_jet_bound (f i) S hK hUnique (hSm i) N
  let M := ∑ i : ι, Mi i
  refine ⟨M,Finset.sum_nonneg (fun i _ => (hMi i).1),?_⟩
  intro i n hn t ht
  have hOne : Mi i ≤ M := Finset.single_le_sum
    (fun j _ => (hMi j).1) (Finset.mem_univ i)
  exact ((hMi i).2 n hn t ht).trans hOne

/-- Complete joint allN high/low budget on opaque paired-index families.
The proof has no endpoint-selection or graph-construction motive. -/
theorem exists_paired_high_low_jet_caps {ι : Type} [Fintype ι]
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (Ch : ι → ι → Tpar → Hi →L[ℝ] Half)
    (Cl : ι → ι → Tpar → Half →L[ℝ] Neg)
    (hCh : ∀ a b, ContDiffOn ℝ ∞ (Ch a b) S)
    (hCl : ∀ a b, ContDiffOn ℝ ∞ (Cl a b) S) :
    ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ι, ∀ n : ℕ,
      n ≤ N → ∀ t ∈ S,
        ‖iteratedFDerivWithin ℝ n (Ch a b) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (Cl a b) S t‖ ≤ M := by
  classical
  intro N
  choose Mh hMh using fun a b : ι =>
    exists_high_compact_jet_bound (Ch a b) S hK hS (hCh a b) N
  choose Ml hMl using fun a b : ι =>
    exists_low_compact_jet_bound (Cl a b) S hK hS (hCl a b) N
  let M := ∑ a : ι, ∑ b : ι, (Mh a b+Ml a b)
  have hPair (a b : ι) : 0 ≤ Mh a b+Ml a b :=
    add_nonneg (hMh a b).1 (hMl a b).1
  have hRow (a : ι) : 0 ≤ ∑ b : ι, (Mh a b+Ml a b) :=
    Finset.sum_nonneg (fun b _ => hPair a b)
  refine ⟨M,Finset.sum_nonneg (fun a _ => hRow a),?_⟩
  intro a b n hn t ht
  have hInner : Mh a b+Ml a b ≤ ∑ c : ι, (Mh a c+Ml a c) :=
    Finset.single_le_sum (fun c _ => hPair a c) (Finset.mem_univ b)
  have hOuter : (∑ c : ι, (Mh a c+Ml a c)) ≤ M :=
    Finset.single_le_sum (fun c _ => hRow c) (Finset.mem_univ a)
  have hOne : Mh a b+Ml a b ≤ M := hInner.trans hOuter
  exact ⟨((hMh a b).2 n hn t ht).trans
      ((le_add_of_nonneg_right (hMl a b).1).trans hOne),
    ((hMl a b).2 n hn t ht).trans
      ((le_add_of_nonneg_left (hMh a b).1).trans hOne)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomNativeBudgets
