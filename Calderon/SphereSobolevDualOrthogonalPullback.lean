import Calderon.SphereSobolevOrthogonalPullback
import Calderon.SphereSobolevDualRiesz

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

theorem sphereSobolevDualPairing_orthogonalPullback (s : ℝ)
    (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereSobolev s) (v : SphereSobolev (-s)) :
    sphereSobolevDualPairing s (sphereSobolevOrthogonalPullbackL s e u)
      (sphereSobolevOrthogonalPullbackL (-s) e v) = sphereSobolevDualPairing s u v := by
  rw [sphereSobolevDualPairing_eq_tsum,sphereSobolevDualPairing_eq_tsum]
  apply tsum_congr
  intro k
  rw [sphereSobolevCoefficientL_orthogonalPullback,sphereSobolevCoefficientL_orthogonalPullback]
  exact (harmonicSphereOrthogonalPullback e k).inner_map_map _ _

theorem sphereSobolevDualPairing_orthogonalPullback_right (s : ℝ)
    (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereSobolev s) (v : SphereSobolev (-s)) :
    sphereSobolevDualPairing s u (sphereSobolevOrthogonalPullbackL (-s) e v) =
      sphereSobolevDualPairing s (sphereSobolevOrthogonalPullbackL s e.symm u) v := by
  have hu : sphereSobolevOrthogonalPullbackL s e
      (sphereSobolevOrthogonalPullbackL s e.symm u) = u := by
    simpa only [LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply s e.symm u
  have h := sphereSobolevDualPairing_orthogonalPullback s e
    (sphereSobolevOrthogonalPullbackL s e.symm u) v
  rw [hu] at h
  exact h

theorem sphereSobolev_eq_of_dualPairing_eq (s : ℝ)
    (v w : SphereSobolev (-s))
    (h : ∀ u : SphereSobolev s, sphereSobolevDualPairing s u v = sphereSobolevDualPairing s u w) :
    v = w := by
  apply ext_inner_left ℝ
  exact h

theorem sphereSobolevDualRieszL_orthogonalPullback (s : ℝ)
    (e : R3 ≃ₗᵢ[ℝ] R3) (ell : StrongDual ℝ (SphereSobolev s)) :
    sphereSobolevDualRieszL s (ell.comp (sphereSobolevOrthogonalPullbackL s e.symm)) =
      sphereSobolevOrthogonalPullbackL (-s) e (sphereSobolevDualRieszL s ell) := by
  apply sphereSobolev_eq_of_dualPairing_eq s
  intro u
  rw [sphereSobolevDualPairing_dualRiesz,sphereSobolevDualPairing_orthogonalPullback_right,
    sphereSobolevDualPairing_dualRiesz]
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic
