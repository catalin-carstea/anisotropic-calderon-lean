import Calderon.ParametricCoerciveInverse
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem isCoercive_of_scalar_energy_lower_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (E : V → V → ℝ)
    (hValue : ∀ u : V, B u u = E u u)
    (hLower : ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖^2 ≤ E u u) : IsCoercive B := by
  obtain ⟨c,hc,hBound⟩ := hLower
  refine ⟨c,hc,?_⟩
  intro u
  have h : c * ‖u‖^2 ≤ B u u := (hBound u).trans_eq (hValue u).symm
  simpa only [pow_two,mul_assoc] using h

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.isCoercive_of_scalar_energy_lower_bound
