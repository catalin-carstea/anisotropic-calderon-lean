import Calderon.ActualReferenceDDHigherGeometryJets

/-! GPT-6.1 Sol. Before-code ../full-first-norm-isolation-upfront-v001.md.
Opaque finite-family norm budget for the actual D proof. No author compiler. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow

/-- A positive finite-family norm budget, with the norm sum kept opaque to users. -/
theorem exists_finite_family_norm_budget {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (A : ι → E) :
    ∃ N : ℝ, 0 < N ∧ ∀ i, ‖A i‖ ≤ N := by
  classical
  let N : ℝ := 1+∑ i : ι, ‖A i‖
  have hSum : 0 ≤ ∑ i : ι, ‖A i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hN : 0 < N := by dsimp only [N]; linarith
  refine ⟨N,hN,?_⟩
  intro i
  have hh := Finset.single_le_sum (fun j _ => norm_nonneg (A j)) (Finset.mem_univ i)
  dsimp only [N]
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSSecondRow
