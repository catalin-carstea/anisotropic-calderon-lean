import Calderon.SphereSobolevCompletion
import Calderon.RealNormedGroupProjectionData

/-! Inverse and norm of the canonical zero decoding: isometry identities only. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevZeroEquiv_apply_symm_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev 0) :
    sphereSobolevZeroEquiv hO hD ((sphereSobolevZeroEquiv hO hD).symm v) = v := by
  exact LinearIsometryEquiv.apply_symm_apply (sphereSobolevZeroEquiv hO hD) v

lemma norm_sphereSobolevZeroEquiv_symm_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev 0) :
    ‖(sphereSobolevZeroEquiv hO hD).symm v‖ = ‖v‖ := by
  exact (sphereSobolevZeroEquiv hO hD).symm.norm_map v

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevZeroEquiv_apply_symm_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevZeroEquiv_symm_apply
