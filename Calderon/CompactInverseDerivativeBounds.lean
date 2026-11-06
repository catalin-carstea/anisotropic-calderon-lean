import Calderon.BanachInverseFamily
import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_compact_iteratedFDeriv_bound (f : E → V) (q : Set E) (hq : IsCompact q)
    (hf : ∀ x ∈ q, ContDiffAt ℝ ∞ f x) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ x ∈ q, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  have hb (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x ∈ q, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
    have hc : ContinuousOn (iteratedFDeriv ℝ n f) q :=
      fun x hx => ((hf x hx).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨C,hC⟩ := hq.exists_bound_of_continuousOn hc
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  let Cn : ℕ → ℝ := fun n => Classical.choose (hb n)
  have hn (n : ℕ) : 0 ≤ Cn n ∧ ∀ x ∈ q, ‖iteratedFDeriv ℝ n f x‖ ≤ Cn n :=
    Classical.choose_spec (hb n)
  refine ⟨∑ i : Fin (N+1), Cn i.val,Finset.sum_nonneg (fun i _ => (hn i.val).1),?_⟩
  intro n hnN x hx
  let i : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hnN⟩
  exact ((hn n).2 x hx).trans
    (Finset.single_le_sum (fun j _ => (hn j.val).1) (Finset.mem_univ i))

variable {X Y F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_compact_banachInverse_derivative_bound
    (A : E → X →L[ℝ] Y) (hA : ContDiff ℝ ∞ A) (q : Set E) (hq : IsCompact q)
    (hi : ∀ x ∈ q, (A x).IsInvertible) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ x ∈ q,
      ‖iteratedFDeriv ℝ n (fun p => (A p).inverse) x‖ ≤ C :=
  exists_compact_iteratedFDeriv_bound _ q hq
    (fun x hx => (hi x hx).contDiffAt_map_inverse.comp x hA.contDiffAt) N

theorem exists_compact_banachWeightedInverse_derivative_bound
    (A : E → X →L[ℝ] Y) (hA : ContDiff ℝ ∞ A)
    (M : E → F →L[ℝ] Y) (hM : ContDiff ℝ ∞ M) (q : Set E) (hq : IsCompact q)
    (hi : ∀ x ∈ q, (A x).IsInvertible) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ x ∈ q,
      ‖iteratedFDeriv ℝ n (fun p => (A p).inverse.comp (M p)) x‖ ≤ C :=
  exists_compact_iteratedFDeriv_bound _ q hq
    (fun x hx => ((hi x hx).contDiffAt_map_inverse.comp x hA.contDiffAt).clm_comp hM.contDiffAt) N
end OAI.AnisotropicCalderon.DirichletFamily
