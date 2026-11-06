import Calderon.ActualAllAngularAtomScalarCaps

/-! Joint cap assembly on abstract real arrays. The proof contains no native
Sobolev spaces, derivatives, norms or inherited normed-space instances. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomRealPairCaps

/-- Merge two proved scalar jet bounds on the same finite-order domain. -/
theorem exists_pair_real_caps {ι T : Type}
    (F G : ι → ℕ → T → ℝ) (S : Set T) (N : ℕ)
    (hF : ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N →
      ∀ t ∈ S, F a n t ≤ M)
    (hG : ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N →
      ∀ t ∈ S, G a n t ≤ M) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      F a n t ≤ M ∧ G a n t ≤ M := by
  obtain ⟨MF, _, hF⟩ := hF
  obtain ⟨MG, _, hG⟩ := hG
  obtain ⟨M, hOne, hFM, hGM, _, _, _⟩ :=
    ActualAllAngularAtomScalarCaps.exists_five_real_upper_bounds MF MG 0 0 0
  refine ⟨M, hOne, ?_⟩
  intro a n hn t ht
  exact ⟨(hF a n hn t ht).trans hFM, (hG a n hn t ht).trans hGM⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomRealPairCaps
