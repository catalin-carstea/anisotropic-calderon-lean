import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SourceJet

variable {D J : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup J] [NormedSpace ℝ J] [FiniteDimensional ℝ J]

theorem mem_range_of_approx (T : D →ₗ[ℝ] J) (v : J)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ f : D, ‖T f - v‖ < ε) :
    v ∈ LinearMap.range T := by
  have hClosure : v ∈ closure (LinearMap.range T : Set J) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨f, hf⟩ := hApprox ε hε
    refine ⟨T f, ⟨f, rfl⟩, ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using hf
  rwa [(LinearMap.range T).closed_of_finiteDimensional.closure_eq] at hClosure

theorem range_eq_of_approx (T : D →ₗ[ℝ] J) (S : Submodule ℝ J)
    (hRange : LinearMap.range T ≤ S)
    (hApprox : ∀ v ∈ S, ∀ ε : ℝ, 0 < ε → ∃ f : D, ‖T f - v‖ < ε) :
    LinearMap.range T = S := by
  apply le_antisymm hRange
  intro v hv
  exact mem_range_of_approx T v (hApprox v hv)

end OAI.AnisotropicCalderon.SourceJet
#print axioms OAI.AnisotropicCalderon.SourceJet.mem_range_of_approx
#print axioms OAI.AnisotropicCalderon.SourceJet.range_eq_of_approx
