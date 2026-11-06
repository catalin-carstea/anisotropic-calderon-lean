import Calderon.SphereSobolevInclusion

/-! The existing native inclusion and original literal endpoint zero values. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevInclusionL_half_negative_apply_zero :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (0 : SphereSobolev (1/2 : ℝ)) = (0 : SphereSobolev (-(1/2 : ℝ))) := by
  exact (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).map_zero

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_half_negative_apply_zero
