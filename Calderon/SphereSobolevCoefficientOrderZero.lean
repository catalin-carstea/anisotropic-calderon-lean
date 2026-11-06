import Calderon.SphereSobolevCompletion
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
lemma sphereSobolevCoefficientL_one_sub_one (k : ℕ) (u : SphereSobolev 0) :
    sphereSobolevCoefficientL ((1:ℝ)-1) k u = sphereSobolevCoefficientL 0 k u := by
  exact congrArg (fun s : ℝ => sphereSobolevCoefficientL s k u) (sub_self (1:ℝ))
end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_one_sub_one
