import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon

/-- One positive bound for all jets through order two on the same compact set. -/
theorem exists_compact_smooth_jet_bound_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ 2 → ∀ t ∈ K,
      ‖iteratedFDeriv ℝ n f t‖ ≤ C := by
  have hb : ∀ n : Fin 3, ∃ Cn : ℝ, ∀ t ∈ K,
      ‖iteratedFDeriv ℝ n.val f t‖ ≤ Cn := by
    intro n
    have hc : Continuous (iteratedFDeriv ℝ n.val f) :=
      hf.continuous_iteratedFDeriv (by simp)
    exact hK.exists_bound_of_continuousOn hc.continuousOn
  choose Cn hCn using hb
  have hsum : 0 ≤ ∑ n : Fin 3, |Cn n| :=
    Finset.sum_nonneg (fun n _ => abs_nonneg (Cn n))
  refine ⟨1 + ∑ n : Fin 3, |Cn n|,
    add_pos_of_pos_of_nonneg zero_lt_one hsum, ?_⟩
  intro n hn t ht
  let k : Fin 3 := ⟨n, Nat.lt_succ_of_le hn⟩
  calc
    ‖iteratedFDeriv ℝ n f t‖ ≤ Cn k := hCn k t ht
    _ ≤ |Cn k| := le_abs_self _
    _ ≤ ∑ j : Fin 3, |Cn j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (Cn j)) (Finset.mem_univ k)
    _ ≤ 1 + ∑ j : Fin 3, |Cn j| := le_add_of_nonneg_left zero_le_one

end OAI.AnisotropicCalderon
