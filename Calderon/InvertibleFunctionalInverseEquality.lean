import Calderon.ParametricCoerciveInverse

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem functionalInverse_eq_inverse (B : V →L[ℝ] StrongDual ℝ V) :
    functionalInverse B = B.inverse := by
  let D : StrongDual ℝ V ≃L[ℝ] V := (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv
  change ((D : StrongDual ℝ V →L[ℝ] V).comp B).inverse.comp (D : StrongDual ℝ V →L[ℝ] V) = B.inverse
  rw [ContinuousLinearMap.inverse_equiv_comp]
  apply ContinuousLinearMap.ext
  intro ell
  change B.inverse (D.symm (D ell)) = B.inverse ell
  exact congrArg B.inverse (D.symm_apply_apply ell)

theorem apply_functionalInverse_of_isInvertible
    (B : V →L[ℝ] StrongDual ℝ V) (hB : B.IsInvertible)
    (ell : StrongDual ℝ V) (v : V) :
    B (functionalInverse B ell) v = ell v := by
  rw [functionalInverse_eq_inverse]
  exact congrArg (fun f : StrongDual ℝ V => f v) (hB.self_apply_inverse ell)

theorem eq_functionalInverse_of_isInvertible
    (B : V →L[ℝ] StrongDual ℝ V) (hB : B.IsInvertible)
    (ell : StrongDual ℝ V) (u : V) (hu : ∀ v, B u v = ell v) :
    u = functionalInverse B ell := by
  have hBu : B u = ell := ContinuousLinearMap.ext hu
  rw [functionalInverse_eq_inverse]
  exact (hB.inverse_apply_eq.mpr hBu.symm).symm

theorem eq_of_bilinear_test_eq_of_isInvertible
    (B : V →L[ℝ] StrongDual ℝ V) (hB : B.IsInvertible)
    (u v : V) (h : ∀ w, B u w = B v w) : u = v :=
  hB.injective (ContinuousLinearMap.ext h)

end OAI.AnisotropicCalderon.DirichletFamily
