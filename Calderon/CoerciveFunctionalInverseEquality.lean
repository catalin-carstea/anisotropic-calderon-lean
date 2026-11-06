import Calderon.ParametricCoerciveInverse

/-! Exact actual weak harmonic radial derivative support; all roots expanded
and sealed before bodies. No desired boundary order estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem isInvertible_and_inverse_eq_functionalInverse
    (B : V →L[ℝ] StrongDual ℝ V) (hB : IsCoercive B) :
    B.IsInvertible ∧ B.inverse = functionalInverse B := by
  let G : StrongDual ℝ V →L[ℝ] V := functionalInverse B
  have hBG : B.comp G = ContinuousLinearMap.id ℝ (StrongDual ℝ V) := by
    apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro v
    exact apply_functionalInverse B hB ell v
  have hGB : G.comp B = ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro u
    exact (eq_functionalInverse B hB (B u) u (fun v => rfl)).symm
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hBG hGB,
    ContinuousLinearMap.inverse_eq hBG hGB⟩

end OAI.AnisotropicCalderon.DirichletFamily
