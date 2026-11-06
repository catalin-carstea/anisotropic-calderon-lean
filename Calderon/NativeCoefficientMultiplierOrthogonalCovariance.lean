import Calderon.NativeNegativeHalfMultiplierOrthogonalCovariance
import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.ContinuousLinearConjugacyInverse

/-! Original full expansion and focused checked proof transfer recorded before source
in EXPANSION-v003.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeNegativeHalfSmoothMultiplier NativeHalfSmoothMultiplier

attribute [local irreducible] nativeNegativeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfSmoothMulL nativeHalfSmoothMulL realHalfOperatorAdjointL
  sphereSobolevOrthogonalPullbackL

lemma nativeNegativeHalfSmoothMulL_congr_data_for_orthogonal_coefficient_covariance
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m₁ m₂ : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm₁ : ∀ x ∈ (ballOpens : Set R3), |m₁.1 x| ≤ M)
    (hg₁ : ∀ x ∈ (ballOpens : Set R3), ‖gradient m₁.1 x‖ ≤ M)
    (hm₂ : ∀ x ∈ (ballOpens : Set R3), |m₂.1 x| ≤ M)
    (hg₂ : ∀ x ∈ (ballOpens : Set R3), ‖gradient m₂.1 x‖ ≤ M)
    (hm : m₁ = m₂) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 m₁ hM hm₁ hg₁ =
      nativeNegativeHalfSmoothMulL hF hO hD τ0 m₂ hM hm₂ hg₂ := by
  cases hm
  rfl


variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (e : R3 ≃ₗᵢ[ℝ] R3) (F G : SmoothCoefficientJets 2)
  (hFG : coefficientSmoothData G = orthogonalSmoothPullback e (coefficientSmoothData F))

include e hFG

lemma nativeNegativeHalfCoefficientMulL_orthogonal_covariance
    (u : SphereSobolev (-(1/2:ℝ))) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e u) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F u) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨N,hN,hn,hgn⟩ := exists_smooth_ball_multiplier_bound
    (orthogonalSmoothPullback e (coefficientSmoothData F))
  have hmG : ∀ x ∈ (ballOpens : Set R3), |(coefficientSmoothData G).1 x| ≤ N := by
    simpa only [hFG] using hn
  have hgG : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coefficientSmoothData G).1 x‖ ≤ N := by
    simpa only [hFG] using hgn
  have hFMap := nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg
  have hGMap := nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 G hN hmG hgG
  have hDataMap := nativeNegativeHalfSmoothMulL_congr_data_for_orthogonal_coefficient_covariance
    hF hO hD τ0 (coefficientSmoothData G)
      (orthogonalSmoothPullback e (coefficientSmoothData F)) hN hmG hgG hn hgn hFG
  have hCov := nativeNegativeHalfSmoothMulL_orthogonal_covariance
    e (coefficientSmoothData F) hM hm hg hN hn hgn hF hO hD τ0 u
  let R : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
  have hLeft := congrArg
    (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (R u)) hGMap
  have hMiddle := congrArg
    (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (R u)) hDataMap
  have hRight := congrArg
    (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => R (A u)) hFMap.symm
  exact hLeft.trans (hMiddle.trans (hCov.trans hRight))


lemma nativeNegativeHalfCoefficientMulL_orthogonal_isInvertible
    (hi : (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).IsInvertible := by
  apply isInvertible_of_continuousLinear_conjugacy
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F)
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G)
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e)
    (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e.symm)
  · intro u
    simpa only [LinearIsometryEquiv.symm_symm] using
      sphereSobolevOrthogonalPullbackL_symm_apply (-(1/2:ℝ)) e.symm u
  · exact sphereSobolevOrthogonalPullbackL_symm_apply (-(1/2:ℝ)) e
  · exact nativeNegativeHalfCoefficientMulL_orthogonal_covariance hcalc hF hO hD τ0 e F G hFG
  · exact hi

lemma nativeNegativeHalfCoefficientMulL_inverse_orthogonal_covariance
    (hi : (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible)
    (u : SphereSobolev (-(1/2:ℝ))) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G).inverse
      (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e u) =
    sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e
      ((nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).inverse u) := by
  have hG := nativeNegativeHalfCoefficientMulL_orthogonal_isInvertible
    hcalc hF hO hD τ0 e F G hFG hi
  apply hG.inverse_apply_eq.mpr
  rw [nativeNegativeHalfCoefficientMulL_orthogonal_covariance hcalc hF hO hD τ0 e F G hFG,
    hi.self_apply_inverse]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfCoefficientMulL_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfCoefficientMulL_orthogonal_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfCoefficientMulL_inverse_orthogonal_covariance

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeNegativeHalfSmoothMulL_congr_data_for_orthogonal_coefficient_covariance
