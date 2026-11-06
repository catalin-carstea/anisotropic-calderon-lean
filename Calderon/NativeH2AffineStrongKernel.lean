import Calderon.NativeH2AffineCorrection

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

lemma nativeH2AffineCorrection_strong_kernel
    (J : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2)
    (hRight : ∀ f : BallSobolev 0, S (J (R f))=f) (f : SphereSobolev (3/2:ℝ)) :
    S (nativeH2AffineCorrectionL J R S P f)=0 := by
  have hEval := congrArg S (nativeH2AffineCorrectionL_apply J R S P f)
  have hSub := S.map_sub (P f) (J (R (S (P f))))
  have hCancel := congrArg (fun y : BallSobolev 0 => S (P f)-y) (hRight (S (P f)))
  exact hEval.trans (hSub.trans (hCancel.trans (sub_self _)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2AffineCorrection_strong_kernel
