import Calderon.CompactInverseDerivativeBounds
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

/-! ## Generic typed finite cancellations and within-jet caps (MATHEMATICS.md §3–§5) -/

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft



section Generic
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Lemma A: lowering commutator cancellation. -/
theorem lowering_commutator_cancellation
    (J : Y →L[ℝ] Z) (Th : X →L[ℝ] Y) (Tl : Y →L[ℝ] Z)
    (Rh : Fin 3 → X →L[ℝ] Y) (Rl : Fin 3 → Y →L[ℝ] Z) (Bh : X →L[ℝ] Y) (Bl : Y →L[ℝ] Z)
    (Ml : Fin 3 → Y →L[ℝ] Y) (Mn : Fin 3 → Z →L[ℝ] Z)
    (Cr : Fin 3 → X →L[ℝ] Y) (Cd : X →L[ℝ] Y) (G : Fin 3 → Y →L[ℝ] Y) (i : Fin 3)
    (h1 : ∀ j v, J (Ml j v) = Mn j (J v))
    (h2 : ∀ j u, J (Cr j u) = Rl j (Th u) - Tl (Rh j u))
    (h3 : ∀ u, J (Cd u) = Bl (Th u) - Tl (Bh u))
    (h4 : ∀ j v, J (G j v) = Tl (Ml j v) - Mn j (Tl v)) (u : X) :
    J (((∑ j : Fin 3, ((Ml j).comp (Cr j) - (G j).comp (Rh j))) +
        (Ml i).comp Cd - (G i).comp Bh) u) =
      ((∑ j : Fin 3, (Mn j).comp (Rl j)) + (Mn i).comp Bl) (Th u) -
        Tl (((∑ j : Fin 3, (Ml j).comp (Rh j)) + (Ml i).comp Bh) u) := by
  have hterm (j : Fin 3) :
      J (Ml j (Cr j u) - G j (Rh j u)) = Mn j (Rl j (Th u)) - Tl (Ml j (Rh j u)) := by
    rw [map_sub, h1, h2, h4, map_sub]
    abel
  have hdeg : J (Ml i (Cd u) - G i (Bh u)) = Mn i (Bl (Th u)) - Tl (Ml i (Bh u)) := by
    rw [map_sub, h1, h3, h4, map_sub]
    abel
  calc
    _ = (∑ j : Fin 3, J (Ml j (Cr j u) - G j (Rh j u))) + J (Ml i (Cd u) - G i (Bh u)) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_sub,
        map_sum] <;> abel
    _ = (∑ j : Fin 3, (Mn j (Rl j (Th u)) - Tl (Ml j (Rh j u)))) +
        (Mn i (Bl (Th u)) - Tl (Ml i (Bh u))) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), hdeg]
    _ = _ := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply, map_add, map_sum, Finset.sum_sub_distrib] <;> abel

/-- Lemma B: raising commutator cancellation. -/
theorem raising_commutator_cancellation
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (Sh : X →L[ℝ] Y) (Sl : Y →L[ℝ] Z)
    (Rh : Fin 3 → X →L[ℝ] Y) (Rl : Fin 3 → Y →L[ℝ] Z) (Bh : X →L[ℝ] Y) (Bl : Y →L[ℝ] Z)
    (Mh : Fin 3 → X →L[ℝ] X) (Ml : Fin 3 → Y →L[ℝ] Y)
    (Cr : Fin 3 → X →L[ℝ] Y) (Cd : X →L[ℝ] Y) (Gh : Fin 3 → X →L[ℝ] X) (i : Fin 3)
    (k1 : ∀ j x, J (Rh j x) = Rl j (I x)) (k1' : ∀ x, J (Bh x) = Bl (I x))
    (k2 : ∀ j x, I (Gh j x) = Sh (Mh j x) - Ml j (Sh x))
    (k3 : ∀ j x, J (Cr j x) = Rl j (Sh x) - Sl (Rh j x))
    (k3' : ∀ x, J (Cd x) = Bl (Sh x) - Sl (Bh x)) (u : X) :
    J (((∑ j : Fin 3, ((Rh j).comp (Gh j) - (Cr j).comp (Mh j))) -
        Bh.comp (Gh i) + Cd.comp (Mh i)) u) =
      ((-∑ j : Fin 3, (Rl j).comp (Ml j)) + Bl.comp (Ml i)) (Sh u) -
        Sl (((-∑ j : Fin 3, (Rh j).comp (Mh j)) + Bh.comp (Mh i)) u) := by
  have hterm (j : Fin 3) :
      J (Rh j (Gh j u) - Cr j (Mh j u)) = -Rl j (Ml j (Sh u)) + Sl (Rh j (Mh j u)) := by
    rw [map_sub, k1, k2, k3, map_sub]
    abel
  have hdeg : -J (Bh (Gh i u)) + J (Cd (Mh i u)) = Bl (Ml i (Sh u)) - Sl (Bh (Mh i u)) := by
    rw [k1', k2, k3', map_sub]
    abel
  calc
    _ = (∑ j : Fin 3, J (Rh j (Gh j u) - Cr j (Mh j u))) +
        (-J (Bh (Gh i u)) + J (Cd (Mh i u))) := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_sub,
        map_sum] <;> abel
    _ = (∑ j : Fin 3, (-Rl j (Ml j (Sh u)) + Sl (Rh j (Mh j u)))) +
        (Bl (Ml i (Sh u)) - Sl (Bh (Mh i u))) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), hdeg]
    _ = _ := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_neg,
        map_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib] <;> abel

end Generic

/-- Lemma K: within-jet caps on a compact UniqueDiffOn set. -/
theorem exists_compact_iteratedFDerivWithin_bound {E V : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (s : Set E) (hs : IsCompact s) (hu : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ ∞ f s) (N : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ x ∈ s, ‖iteratedFDerivWithin ℝ n f s x‖ ≤ M := by
  have hb (n : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x ∈ s, ‖iteratedFDerivWithin ℝ n f s x‖ ≤ M := by
    have hc : ContinuousOn (iteratedFDerivWithin ℝ n f s) s :=
      hf.continuousOn_iteratedFDerivWithin (by simp) hu
    obtain ⟨M,hM⟩ := hs.exists_bound_of_continuousOn hc
    exact ⟨max M 0,le_max_right _ _,fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  let Mn : ℕ → ℝ := fun n => Classical.choose (hb n)
  have hn (n : ℕ) : 0 ≤ Mn n ∧ ∀ x ∈ s, ‖iteratedFDerivWithin ℝ n f s x‖ ≤ Mn n :=
    Classical.choose_spec (hb n)
  refine ⟨∑ i : Fin (N+1), Mn i.val,Finset.sum_nonneg (fun i _ => (hn i.val).1),?_⟩
  intro n hnN x hx
  let i : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hnN⟩
  exact ((hn n).2 x hx).trans
    (Finset.single_le_sum (fun j _ => (hn j.val).1) (Finset.mem_univ i))


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
