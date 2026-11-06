import Calderon.NativeSmoothMultiplierOrthogonalCovariance
import Calderon.NativeNegativeHalfSmoothMultiplier
import Calderon.SphereSobolevDualOrthogonalPullback

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHalfSmoothMultiplier NativeNegativeHalfSmoothMultiplier

variable (e : R3 ≃ₗᵢ[ℝ] R3) (m : SmoothData) {M N : ℝ}
  (hM : 0 ≤ M) (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
  (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
  (hN : 0 ≤ N)
  (hn : ∀ x ∈ (ballOpens : Set R3), |(orthogonalSmoothPullback e m).1 x| ≤ N)
  (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient (orthogonalSmoothPullback e m).1 x‖ ≤ N)

lemma nativeNegativeHalfSmoothMulL_orthogonal_covariance
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SphereSobolev (-(1/2:ℝ))) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (orthogonalSmoothPullback e m) hN hn hgn
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e u) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) := by
  apply ext_inner_right ℝ
  intro v
  let z : SphereSobolev (1/2:ℝ) := sphereSobolevOrthogonalPullbackL (1/2:ℝ) e.symm v
  have hv : sphereSobolevOrthogonalPullbackL (1/2:ℝ) e z = v := by
    simpa only [LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply (1/2:ℝ) e.symm v
  change sphereSobolevDualPairing (-(1/2:ℝ))
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 (orthogonalSmoothPullback e m) hN hn hgn
        (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e u)) v =
    sphereSobolevDualPairing (-(1/2:ℝ))
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u)) v
  rw [← hv,sphereSobolevDualPairing_nativeNegativeHalfSmoothMulL,
    nativeHalfSmoothMulL_orthogonal_covariance e m hM hm hg hN hn hgn]
  have hPair := sphereSobolevDualPairing_orthogonalPullback (-(1/2:ℝ)) e
  rw [neg_neg] at hPair
  have hleft : sphereSobolevDualPairing (-(1/2:ℝ))
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e u)
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg z)) =
      sphereSobolevDualPairing (-(1/2:ℝ)) u
        (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg z) := by
    exact hPair u (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg z)
  have hright : sphereSobolevDualPairing (-(1/2:ℝ))
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u))
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e z) =
      sphereSobolevDualPairing (-(1/2:ℝ))
        (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) z := by
    exact hPair (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u) z
  have hmul := sphereSobolevDualPairing_nativeNegativeHalfSmoothMulL
    hF hO hD τ0 m hM hm hg u z
  exact hleft.trans (hmul.symm.trans hright.symm)

lemma nativeNegativeHalfSmoothMulL_comp_orthogonalPullback
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    (nativeNegativeHalfSmoothMulL hF hO hD τ0 (orthogonalSmoothPullback e m) hN hn hgn).comp
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e) =
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e).comp
      (nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg) := by
  apply ContinuousLinearMap.ext
  intro u
  exact nativeNegativeHalfSmoothMulL_orthogonal_covariance e m hM hm hg hN hn hgn hF hO hD τ0 u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfSmoothMulL_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfSmoothMulL_comp_orthogonalPullback
