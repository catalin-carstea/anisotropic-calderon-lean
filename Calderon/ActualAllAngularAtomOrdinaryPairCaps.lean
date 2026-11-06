import Calderon.ActualLeadingPhysicalSignedSecondForm
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualAllAngularAtomNativeBudgets
import Calderon.ActualAllAngularAtomOrdinaryCaps
import Calderon.ActualAllAngularAtomRealPairCaps

/-! Complete ordinary high/low pair caps as a native assembly boundary.
No final cap callback, metric/data packet, room constructor or norm change. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomOrdinaryPairCaps
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

/-- A complete uniform cap for an ordinary high/low pair. This theorem can
be used twice for the four ordinary families, before adding the gained pair. -/
theorem exists_high_low_atom_family_caps {ι : Type} [Fintype ι]
    (S : Set Tpar) (hK : IsCompact S) (hS : UniqueDiffOn ℝ S)
    (FHi : Tpar → ι → Hi →L[ℝ] Half)
    (FLo : Tpar → ι → Half →L[ℝ] Neg)
    (hHigh : ∀ a : ι, ContDiffOn ℝ ∞ (fun s => FHi s a) S)
    (hLow : ∀ a : ι, ContDiffOn ℝ ∞ (fun s => FLo s a) S) :
    ∀ N : ℕ, ∃ M : ℝ, 1 ≤ M ∧
      ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
        ‖iteratedFDerivWithin ℝ n (fun s => FHi s a) S t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (fun s => FLo s a) S t‖ ≤ M := by
  intro N
  exact @ActualAllAngularAtomRealPairCaps.exists_pair_real_caps ι Tpar
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => FHi s a) S t‖)
    (fun a n t => ‖iteratedFDerivWithin ℝ n (fun s => FLo s a) S t‖)
    S N
    (@ActualAllAngularAtomOrdinaryCaps.exists_high_atom_family_caps
      ι (inferInstance : Fintype ι) FHi S hK hS hHigh N)
    (@ActualAllAngularAtomOrdinaryCaps.exists_low_atom_family_caps
      ι (inferInstance : Fintype ι) FLo S hK hS hLow N)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomOrdinaryPairCaps
