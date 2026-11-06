import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSQuarticBound

/-! The existing standard norm at the exact original Half/Neg pairing type.
No norm instance is registered, replaced or normalized to another convention. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPairingNormDiagnostic
open SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

/-- Explicit application of Mathlib's original standard operator norm. -/
def standardPairingNorm (P : Half →L[ℝ] (Neg →L[ℝ] ℝ)) : ℝ :=
  @Norm.norm (Half →L[ℝ] (Neg →L[ℝ] ℝ))
    (ContinuousLinearMap.hasOpNorm (E := Half) (F := Neg →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)) P

/-- The complete infimum-of-bounds formula at the exact native pairing type. -/
lemma standardPairingNorm_eq_sInf (P : Half →L[ℝ] (Neg →L[ℝ] ℝ)) :
    standardPairingNorm P =
      sInf { c : ℝ | 0 ≤ c ∧ ∀ x : Half, ‖P x‖ ≤ c * ‖x‖ } := rfl

/-- This is the norm expression used by the existing generic quartic APIs. -/
def genericBilinearNorm {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : H →L[ℝ] N →L[ℝ] ℝ) : ℝ := ‖P‖

lemma genericBilinearNorm_nonneg {H N : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : H →L[ℝ] N →L[ℝ] ℝ) : 0 ≤ genericBilinearNorm P := norm_nonneg P

/-- Direct definitional agreement, without a different norm or conversion axiom. -/
lemma standardPairingNorm_eq_generic (P : Half →L[ℝ] (Neg →L[ℝ] ℝ)) :
    standardPairingNorm P = genericBilinearNorm P := rfl

/-- The comparison includes the actual original native dual-pairing map. -/
lemma native_pairing_norm_eq_generic :
    standardPairingNorm PL = genericBilinearNorm PL := rfl

lemma standardPairingNorm_nonneg (P : Half →L[ℝ] (Neg →L[ℝ] ℝ)) :
    0 ≤ standardPairingNorm P := genericBilinearNorm_nonneg P

lemma native_pairing_norm_nonneg : 0 ≤ standardPairingNorm PL :=
  standardPairingNorm_nonneg PL

/-- A generic standard-norm cap transports without an altered inequality. -/
lemma standardPairingNorm_le_of_generic (P : Half →L[ℝ] (Neg →L[ℝ] ℝ)) (M : ℝ)
    (h : genericBilinearNorm P ≤ M) : standardPairingNorm P ≤ M := h

/-- Exact native specialization of the existing four-pairing bound and norm.
This retains all four rows, all five original operator caps and the same M. -/
lemma abs_four_native_pairings_le {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : ι → E →L[ℝ] Half) (G : ι → ι → E →L[ℝ] Half)
    (AL : ι → Half →L[ℝ] Neg) (Cl : ι → ι → Half →L[ℝ] Neg)
    (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ i, ‖B i‖ ≤ M)
    (hG : ∀ i j, ‖G i j‖ ≤ M) (hAL : ∀ i, ‖AL i‖ ≤ M)
    (hCl : ∀ i j, ‖Cl i j‖ ≤ M) (u : E) (i j k l : ι) :
    |PL (A j u) (Cl i k (A l u))+
      PL (A j u) (AL k (G i l u))+
      PL (G k j u) (AL l (B i u))+
      PL (B k u) (Cl j l (B i u))| ≤
        4*standardPairingNorm PL*M^3*‖u‖^2 := by
  exact ActualHigherSQuarticBound.abs_four_pairings_le PL A B G AL Cl M hM
    hA hB hG hAL hCl u i j k l

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSPairingNormDiagnostic
