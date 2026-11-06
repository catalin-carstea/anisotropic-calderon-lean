import Calderon.NativeStrongDirichletInverseInclusion

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-STRONG-INVERSE-FORCING-COMPOSITION-EXPANSION-v001.md. Literal generic typed composition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def nativeStrongDirichletInverseForcingCompositionL (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (N : Y →L[ℝ] BallSobolev s) (U : X →L[ℝ] Y) :
    X →L[ℝ] BallSobolev (s+2) :=
  (nativeStrongDirichletInverseInclusionL s A).comp (N.comp U)

lemma nativeStrongDirichletInverseForcingCompositionL_apply (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (N : Y →L[ℝ] BallSobolev s) (U : X →L[ℝ] Y) (f : X) :
    nativeStrongDirichletInverseForcingCompositionL s A N U f =
      (A.inverse (N (U f)) : BallSobolev (s+2)) := rfl

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseForcingCompositionL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseForcingCompositionL_apply
