import Calderon.CompactInverseDerivativeBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X Y0 Y1 : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y0] [NormedSpace ℝ Y0]
  [NormedAddCommGroup Y1] [NormedSpace ℝ Y1]

lemma exists_compact_finite_pair_iteratedFDeriv_bound
    (C0 : Fin 3 → Fin 3 → X → Y0) (C1 : Fin 3 → Fin 3 → X → Y1)
    (K : Set X) (hK : IsCompact K)
    (hSmooth0 : ∀ i j : Fin 3, ∀ p ∈ K, ContDiffAt ℝ ∞ (C0 i j) p)
    (hSmooth1 : ∀ i j : Fin 3, ∀ p ∈ K, ContDiffAt ℝ ∞ (C1 i j) p) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ∀ i j : Fin 3, ∀ k : ℕ, k ≤ N →
      ‖iteratedFDeriv ℝ k (C0 i j) p‖ ≤ M ∧
      ‖iteratedFDeriv ℝ k (C1 i j) p‖ ≤ M := by
  classical
  have hb (i j : Fin 3) : ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (C0 i j) p‖ ≤ M ∧ ‖iteratedFDeriv ℝ k (C1 i j) p‖ ≤ M := by
    obtain ⟨M0,hM0,hb0⟩ := exists_compact_iteratedFDeriv_bound (C0 i j) K hK (hSmooth0 i j) N
    obtain ⟨M1,hM1,hb1⟩ := exists_compact_iteratedFDeriv_bound (C1 i j) K hK (hSmooth1 i j) N
    refine ⟨M0+M1,add_nonneg hM0 hM1,?_⟩
    intro k hk p hp
    exact ⟨(hb0 k hk p hp).trans (le_add_of_nonneg_right hM1),
      (hb1 k hk p hp).trans (le_add_of_nonneg_left hM0)⟩
  let Mij : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hb i j)
  have hM (i j : Fin 3) : 0 ≤ Mij i j ∧ ∀ k : ℕ, k ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ k (C0 i j) p‖ ≤ Mij i j ∧
      ‖iteratedFDeriv ℝ k (C1 i j) p‖ ≤ Mij i j := Classical.choose_spec (hb i j)
  have hSum (i : Fin 3) : 0 ≤ ∑ j : Fin 3, Mij i j :=
    Finset.sum_nonneg (fun j _ => (hM i j).1)
  refine ⟨∑ i : Fin 3, ∑ j : Fin 3, Mij i j,
    Finset.sum_nonneg (fun i _ => hSum i),?_⟩
  intro p hp i j k hk
  have hPair : Mij i j ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, Mij i' j' :=
    (Finset.single_le_sum (fun j' _ => (hM i j').1) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => hSum i') (Finset.mem_univ i))
  exact ⟨((hM i j).2 k hk p hp).1.trans hPair,
    ((hM i j).2 k hk p hp).2.trans hPair⟩

lemma exists_commonRadius_finite_pair_endpoint_jets
    (C0 : Fin 3 → Fin 3 → X → Y0) (C1 : Fin 3 → Fin 3 → X → Y1)
    (K : ℝ → Set X) (hK : ∀ δ : ℝ, IsCompact (K δ)) (room : X → Prop) (rho : ℝ)
    (hRadius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ rho ∧ ∀ p ∈ K δ,
      room p ∧ ∀ i j : Fin 3, ContDiffAt ℝ ∞ (C0 i j) p ∧ ContDiffAt ℝ ∞ (C1 i j) p) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ rho ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K δ,
        room p ∧ ∀ i j : Fin 3, ContDiffAt ℝ ∞ (C0 i j) p ∧ ContDiffAt ℝ ∞ (C1 i j) p ∧
          ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k (C0 i j) p‖ ≤ M ∧
            ‖iteratedFDeriv ℝ k (C1 i j) p‖ ≤ M := by
  refine Exists.elim hRadius ?_
  intro δ hChosen
  have hδ : 0 < δ := And.left hChosen
  have hδrho : δ ≤ rho := And.left (And.right hChosen)
  have hRoom := And.right (And.right hChosen)
  have hSmooth0 : ∀ i j : Fin 3, ∀ p ∈ K δ, ContDiffAt ℝ ∞ (C0 i j) p :=
    fun i j p hp => ((hRoom p hp).2 i j).1
  have hSmooth1 : ∀ i j : Fin 3, ∀ p ∈ K δ, ContDiffAt ℝ ∞ (C1 i j) p :=
    fun i j p hp => ((hRoom p hp).2 i j).2
  refine ⟨δ,hδ,hδrho,?_⟩
  intro N
  obtain ⟨M,hM,hBound⟩ := exists_compact_finite_pair_iteratedFDeriv_bound C0 C1 (K δ)
    (hK δ) hSmooth0 hSmooth1 N
  refine ⟨M,hM,?_⟩
  intro p hp
  refine ⟨(hRoom p hp).1,?_⟩
  intro i j
  exact ⟨hSmooth0 i j p hp,hSmooth1 i j p hp,hBound p hp i j⟩

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.exists_compact_finite_pair_iteratedFDeriv_bound
#print axioms OAI.AnisotropicCalderon.DirichletFamily.exists_commonRadius_finite_pair_endpoint_jets
