import Calderon.NativeStrongDirichletInclusion

/-! Exact existing total inverse plus native inclusion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily

def nativeStrongDirichletInverseInclusionL (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s) :
    BallSobolev s →L[ℝ] BallSobolev (s+2) :=
  (nativeStrongDirichletInclusionL s).comp A.inverse

lemma nativeStrongDirichletInverseInclusionL_apply (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s) (f : BallSobolev s) :
    nativeStrongDirichletInverseInclusionL s A f = (A.inverse f : BallSobolev (s+2)) := rfl

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseInclusionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseInclusionL_apply
