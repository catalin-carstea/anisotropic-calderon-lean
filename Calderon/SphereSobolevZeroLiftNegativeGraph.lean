import Calderon.SphereSobolevZeroEquivIdentities
import Calderon.SphereSobolevHalfZeroNegativeInclusion

/-! Full before-source: day-oct13/actual-physical-full-allocation-author-oct16-v001/
EXPANSION-zero-lift-negative-graph-v061.md. Original native cancellation and inclusion only. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevZeroEquiv_symm_negative_inclusion_of_half_inclusion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev (1/2 : ℝ)) (x : SphereSobolev 0)
    (hx : sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v = x) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD ((sphereSobolevZeroEquiv hO hD).symm x)) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v := by
  have hCancel := sphereSobolevZeroEquiv_apply_symm_apply hO hD x
  have hMiddle := hCancel.trans hx.symm
  have hIncluded := congrArg
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) hMiddle
  exact hIncluded.trans (sphereSobolevInclusionL_half_zero_neg_half_apply v)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevZeroEquiv_symm_negative_inclusion_of_half_inclusion
