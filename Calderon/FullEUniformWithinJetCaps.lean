import Calderon.ActualPiMixedWeakEndpointCore
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open ActualAngularPiDraft

/-- One exact finite within-jet cap for three ordered pairs of smooth finite families. -/
theorem exists_uniform_six_family_within_jet_cap
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : Set X) (hS : IsCompact S) (hU : UniqueDiffOn ℝ S)
    (a1 a2 a3 : Fin 3 → Fin 3 → X → Y)
    (b1 b2 b3 : Fin 3 → Fin 3 → X → Z)
    (ha1 : ∀ i j, ContDiffOn ℝ ∞ (a1 i j) S) (hb1 : ∀ i j, ContDiffOn ℝ ∞ (b1 i j) S)
    (ha2 : ∀ i j, ContDiffOn ℝ ∞ (a2 i j) S) (hb2 : ∀ i j, ContDiffOn ℝ ∞ (b2 i j) S)
    (ha3 : ∀ i j, ContDiffOn ℝ ∞ (a3 i j) S) (hb3 : ∀ i j, ContDiffOn ℝ ∞ (b3 i j) S)
    (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ n (a1 i j) S x‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (b1 i j) S x‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (a2 i j) S x‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (b2 i j) S x‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (a3 i j) S x‖ ≤ M ∧
      ‖iteratedFDerivWithin ℝ n (b3 i j) S x‖ ≤ M := by
  obtain ⟨M1,hM1,h1⟩ := v016_exists_uniform_cap_two S hS hU a1 b1 ha1 hb1 N
  obtain ⟨M2,hM2,h2⟩ := v016_exists_uniform_cap_two S hS hU a2 b2 ha2 hb2 N
  obtain ⟨M3,hM3,h3⟩ := v016_exists_uniform_cap_two S hS hU a3 b3 ha3 hb3 N
  have hsum : 0 ≤ M1+M2+M3 := add_nonneg (add_nonneg hM1 hM2) hM3
  have hle1 : M1 ≤ M1+M2+M3 :=
    (le_add_of_nonneg_right hM2 : M1 ≤ M1+M2).trans (le_add_of_nonneg_right hM3)
  have hle2 : M2 ≤ M1+M2+M3 :=
    (le_add_of_nonneg_left hM1 : M2 ≤ M1+M2).trans (le_add_of_nonneg_right hM3)
  have hle3 : M3 ≤ M1+M2+M3 := le_add_of_nonneg_left (add_nonneg hM1 hM2)
  refine ⟨M1+M2+M3,hsum,?_⟩
  intro i j n hn x hx
  exact ⟨(h1 i j n hn x hx).1.trans hle1,(h1 i j n hn x hx).2.trans hle1,
    (h2 i j n hn x hx).1.trans hle2,(h2 i j n hn x hx).2.trans hle2,
    (h3 i j n hn x hx).1.trans hle3,(h3 i j n hn x hx).2.trans hle3⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly.exists_uniform_six_family_within_jet_cap
