import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevInclusionL_half_zero_neg_half_apply
    (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v := by
  have h := sphereSobolevInclusionL_trans
    (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num)
  have hv := DFunLike.congr_fun h v
  simpa only [ContinuousLinearMap.comp_apply] using hv

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_half_zero_neg_half_apply
