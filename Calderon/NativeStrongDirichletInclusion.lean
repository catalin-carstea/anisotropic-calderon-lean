import Calderon.NativeLowerOrderProjection

/-! Literal native subtype inclusion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily

def nativeStrongDirichletInclusionL (s : ℕ) :
    StrongDirichletSpace s →L[ℝ] BallSobolev (s+2) := by
  let L : StrongDirichletSpace s →ₗ[ℝ] BallSobolev (s+2) :=
    { toFun := fun U => (U : BallSobolev (s+2))
      map_add' := fun U V => rfl
      map_smul' := fun c U => rfl }
  exact L.mkContinuous 1 (fun U => by
    change ‖(U : BallSobolev (s+2))‖ ≤ 1 * ‖U‖
    rw [one_mul]
    exact le_rfl)

lemma nativeStrongDirichletInclusionL_apply (s : ℕ) (U : StrongDirichletSpace s) :
    nativeStrongDirichletInclusionL s U = (U : BallSobolev (s+2)) := rfl

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInclusionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInclusionL_apply
