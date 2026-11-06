import Calderon.NativeStrongDirichletInverseForcingComposition

/-! Laws of the native composition. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma nativeStrongDirichletInverseForcingCompositionL_map_add (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (N : Y →L[ℝ] BallSobolev s) (U : X →L[ℝ] Y) (f g : X) :
    nativeStrongDirichletInverseForcingCompositionL s A N U (f+g) =
      nativeStrongDirichletInverseForcingCompositionL s A N U f +
        nativeStrongDirichletInverseForcingCompositionL s A N U g :=
  (nativeStrongDirichletInverseForcingCompositionL s A N U).map_add f g

lemma nativeStrongDirichletInverseForcingCompositionL_map_smul (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (N : Y →L[ℝ] BallSobolev s) (U : X →L[ℝ] Y) (c : ℝ) (f : X) :
    nativeStrongDirichletInverseForcingCompositionL s A N U (c • f) =
      c • nativeStrongDirichletInverseForcingCompositionL s A N U f :=
  (nativeStrongDirichletInverseForcingCompositionL s A N U).map_smul c f

lemma continuous_nativeStrongDirichletInverseForcingCompositionL (s : ℕ)
    (A : StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (N : Y →L[ℝ] BallSobolev s) (U : X →L[ℝ] Y) :
    Continuous (fun f : X => nativeStrongDirichletInverseForcingCompositionL s A N U f) :=
  (nativeStrongDirichletInverseForcingCompositionL s A N U).continuous

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseForcingCompositionL_map_add
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeStrongDirichletInverseForcingCompositionL_map_smul
#print axioms OAI.AnisotropicCalderon.DirichletFamily.continuous_nativeStrongDirichletInverseForcingCompositionL
