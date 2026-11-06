import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualAllAngularAtomNativeBudgets

/-! Complete finite paired-low family construction on opaque high families.
No actual metric/data/germ/room-choice context enters this module. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomPairedLow
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

attribute [local irreducible] sphereSobolevInclusionL v016TransposeL

private theorem exists_smooth_paired_low_full
    (S : Set Tpar) (hS : UniqueDiffOn ℝ S)
    (Ch Dh : Tpar → Hi →L[ℝ] Half)
    (hCh : ContDiffOn ℝ ∞ Ch S) (hDh : ContDiffOn ℝ ∞ Dh S)
    (hAdj : ∀ t ∈ S, ∀ u v : Hi,
      PP (IH v) (JL (Ch t u)) = PP (IH u) (JL (Dh t v))) :
    ∃ Cl : Tpar → Half →L[ℝ] Neg,
      ContDiffOn ℝ ∞ Cl S ∧ ∀ t ∈ S,
        (Cl t).comp IH = (JL).comp (Ch t) ∧
        (I33).comp (Cl t) = (v016TransposeL (Dh t)).comp JL ∧
        ‖Cl t‖ ≤ (‖v016TransposeL (Dh t)‖+‖Ch t‖)/2 ∧
        ‖Cl t‖ ≤ (‖Dh t‖+‖Ch t‖)/2 :=
  v016_exists_contDiffOn_lowEndpoint S hS Ch Dh hCh hDh hAdj


/-- All ordered-pair smooth lows, both inclusion orientations, both native
midpoint bounds, and every finite high/low jet cap on one compact room. For an
index set of sixteen atoms the universal pairs cover all256 ordered pairs.
The structural premises are discharged inside the actual room producer. -/
theorem exists_finite_paired_low_family {ι : Type} [Fintype ι]
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (Ch : ι → ι → Tpar → Hi →L[ℝ] Half)
    (hCh : ∀ a b, ContDiffOn ℝ ∞ (Ch a b) S)
    (hAdj : ∀ a b t, t ∈ S → ∀ u v : Hi,
      PP (IH v) (JL (Ch a b t u)) = PP (IH u) (JL (Ch b a t v))) :
    ∃ Cl : ι → ι → Tpar → Half →L[ℝ] Neg,
      (∀ a b, ContDiffOn ℝ ∞ (Cl a b) S ∧ ∀ t ∈ S,
        (Cl a b t).comp IH = (JL).comp (Ch a b t) ∧
        (I33).comp (Cl a b t) = (v016TransposeL (Ch b a t)).comp JL ∧
        ‖Cl a b t‖ ≤ (‖Ch a b t‖+‖Ch b a t‖)/2) ∧
      (∀ a b t, t ∈ S →
        ‖Cl a b t‖ ≤ (‖v016TransposeL (Ch b a t)‖+‖Ch a b t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ι, ∀ n : ℕ,
        n ≤ N → ∀ t ∈ S,
          ‖iteratedFDerivWithin ℝ n (Ch a b) S t‖ ≤ M ∧
          ‖iteratedFDerivWithin ℝ n (Cl a b) S t‖ ≤ M) := by
  classical
  have hLow (a b : ι) := exists_smooth_paired_low_full
    S hS (Ch a b) (Ch b a) (hCh a b) (hCh b a) (hAdj a b)
  choose Cl hCl using hLow
  refine ⟨Cl,?_,?_,?_⟩
  · intro a b
    refine ⟨(hCl a b).1,?_⟩
    intro t ht
    exact ⟨((hCl a b).2 t ht).1,((hCl a b).2 t ht).2.1,
      by simpa only [add_comm] using ((hCl a b).2 t ht).2.2.2⟩
  · intro a b t ht
    exact ((hCl a b).2 t ht).2.2.1
  · exact ActualAllAngularAtomNativeBudgets.exists_paired_high_low_jet_caps
      S hK hS Ch Cl hCh (fun a b => (hCl a b).1)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomPairedLow
