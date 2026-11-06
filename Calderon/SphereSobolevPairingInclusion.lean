import Calderon.SphereSobolevPairing
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

theorem sphereSobolevDualPairing_inclusion_eq_inner_zero
    (s : ℝ) (hs : 0 ≤ s) (u v : SphereSobolev s) :
    sphereSobolevDualPairing (-s)
      (sphereSobolevInclusionL s (-s) (neg_le_self hs) u) v =
      ⟪sphereSobolevInclusionL s 0 hs u,sphereSobolevInclusionL s 0 hs v⟫_ℝ := by
  rw [sphereSobolevDualPairing_eq_tsum,inner_sphereSobolev 0]
  simp only [sphereSobolevCoefficientL_inclusion,
    besselWeight_zero_order,one_pow,one_mul]
  simp only [sphereSobolevCoefficientL,neg_neg]

end OAI.AnisotropicCalderon.SphereHarmonic
