import Calderon.CompactInverseDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace OAI.AnisotropicCalderon

lemma exists_nonneg_bound_iteratedFDerivWithin_on_compact
    {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : X → F) (S C : Set X) (hG : ContDiffOn ℝ ∞ G S) (hUnique : UniqueDiffOn ℝ S)
    (hC : IsCompact C) (hCS : C ⊆ S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ C, ∀ n : ℕ, n ≤ N → ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M := by
  classical
  have hFinite (n : Fin (N+1)) : ∃ b : ℝ, 0 ≤ b ∧
      ∀ z ∈ C, ‖iteratedFDerivWithin ℝ n.val G S z‖ ≤ b := by
    have hCont : ContinuousOn (iteratedFDerivWithin ℝ n.val G S) C :=
      (hG.continuousOn_iteratedFDerivWithin (by simp) hUnique).mono hCS
    obtain ⟨b,hb⟩ := hC.exists_bound_of_continuousOn hCont
    exact ⟨max b 0,le_max_right _ _,fun z hz => (hb z hz).trans (le_max_left _ _)⟩
  choose bs hbs hb using hFinite
  let M : ℝ := ∑ n : Fin (N+1), bs n
  have hM : 0 ≤ M := Finset.sum_nonneg (fun n _ => hbs n)
  refine ⟨M,hM,?_⟩
  intro z hz n hn
  let k : Fin (N+1) := ⟨n,by omega⟩
  exact (hb k z hz).trans
    (Finset.single_le_sum (fun l _ => hbs l) (Finset.mem_univ k))


end OAI.AnisotropicCalderon
