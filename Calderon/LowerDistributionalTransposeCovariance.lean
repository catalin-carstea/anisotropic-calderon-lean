import Calderon.SphereSobolevDualOrthogonalPullback
import Calderon.ActualReferenceLowerBoundaryTranspose

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "P" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local irreducible] harmonicSphereSubspace sphereSobolevDualPairing
  sphereLowerDistributionalTranspose sphereSobolevOrthogonalPullbackL

theorem lowerDistributionalTranspose_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (Q C : Half →L[ℝ] Neg)
    (h : Q.comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e).comp C) :
    (sphereLowerDistributionalTranspose Q).comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e).comp
        (sphereLowerDistributionalTranspose C) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro v
  let w : Half := sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e.symm v
  have hU : sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e w = v := by
    simpa only [w,LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply (1/2 : ℝ) e.symm v
  have hCov : Q v = sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e (C w) := by
    have hv := congrArg (fun A : Half →L[ℝ] Neg => A w) h
    simpa only [ContinuousLinearMap.comp_apply,hU] using hv
  change P v (sphereLowerDistributionalTranspose Q
      (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e u)) =
    P v (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e (sphereLowerDistributionalTranspose C u))
  calc
    _ = P (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e u) (Q v) :=
      (sphereSobolevDualPairing_lower_distributionalTranspose Q v
        (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e u)).symm
    _ = P (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e u)
        (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e (C w)) := congrArg (P _) hCov
    _ = P u (C w) := sphereSobolevDualPairing_orthogonalPullback (1/2 : ℝ) e u (C w)
    _ = P w (sphereLowerDistributionalTranspose C u) :=
      sphereSobolevDualPairing_lower_distributionalTranspose C w u
    _ = _ := (sphereSobolevDualPairing_orthogonalPullback_right (1/2 : ℝ) e v
      (sphereLowerDistributionalTranspose C u)).symm

theorem neg_lowerDistributionalTranspose_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (Q C : Half →L[ℝ] Neg)
    (h : Q.comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e).comp C) :
    (-sphereLowerDistributionalTranspose Q).comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e) =
      (sphereSobolevOrthogonalPullbackL (-(1/2 : ℝ)) e).comp
        (-sphereLowerDistributionalTranspose C) := by
  have ht := lowerDistributionalTranspose_orthogonal_covariance e Q C h
  apply ContinuousLinearMap.ext
  intro u
  have hu := congrArg (fun A : Half →L[ℝ] Neg => -(A u)) ht
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,map_neg] using hu

end OAI.AnisotropicCalderon.SphereHarmonic
