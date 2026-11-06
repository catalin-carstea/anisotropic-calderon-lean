import Calderon.ActualAllAngularAtomScalarCaps

/-! The original six-cap conclusion on abstract real arrays. Native derivative
norms enter only through a later single specialization of this proved theorem. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomRealSixCaps

/-- Merge two ordinary-pair caps and one ordered gained-pair cap. The output
keeps the exact original ordinary-four/gained-two conjunction and index order. -/
theorem exists_six_real_caps {ι T : Type}
    (AHi BHi ALo BLo : ι → ℕ → T → ℝ)
    (GHi GLo : ι → ι → ℕ → T → ℝ)
    (S : Set T) (N : ℕ)
    (hA : ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      AHi a n t ≤ M ∧ ALo a n t ≤ M)
    (hB : ∃ M : ℝ, 1 ≤ M ∧ ∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      BHi a n t ≤ M ∧ BLo a n t ≤ M)
    (hG : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
      GHi a b n t ≤ M ∧ GLo a b n t ≤ M) :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ a : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
        AHi a n t ≤ M ∧
        ALo a n t ≤ M ∧
        BHi a n t ≤ M ∧
        BLo a n t ≤ M) ∧
      (∀ a b : ι, ∀ n : ℕ, n ≤ N → ∀ t ∈ S,
        GHi a b n t ≤ M ∧
        GLo a b n t ≤ M) := by
  obtain ⟨MA, _, hA⟩ := hA
  obtain ⟨MB, _, hB⟩ := hB
  obtain ⟨MG, _, hG⟩ := hG
  obtain ⟨M, hOne, hAM, hBM, hGM, _, _⟩ :=
    ActualAllAngularAtomScalarCaps.exists_five_real_upper_bounds MA MB MG 0 0
  refine ⟨M, hOne, ?_, ?_⟩
  · intro a n hn t ht
    exact ⟨((hA a n hn t ht).1).trans hAM, ((hA a n hn t ht).2).trans hAM,
      ((hB a n hn t ht).1).trans hBM, ((hB a n hn t ht).2).trans hBM⟩
  · intro a b n hn t ht
    exact ⟨((hG a b n hn t ht).1).trans hGM, ((hG a b n hn t ht).2).trans hGM⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomRealSixCaps
