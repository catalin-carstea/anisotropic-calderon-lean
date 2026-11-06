import Calderon.NativeNegativeHalfSmoothMultiplier

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeNegativeHalfSmoothMultiplier
open EnergyBridge DirichletFamily SphereHarmonic SpectralCoreRegularity NativeHalfSmoothMultiplier

theorem nativeNegativeHalfSmoothMulL_zero_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (z : SphereSobolev 0) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) z) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (smoothSphereValue m) ((sphereSobolevZeroEquiv hO hD).symm z))) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let K : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let A := nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let B := nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let C := sphereContinuousScalarMulL (smoothSphereValue m)
  have htrans (u : SphereSobolev (1/2 : ℝ)) : J (I u) = K u := by
    exact congrArg (fun L : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => L u)
      (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  change B (J z) = J (Z (C (Z.symm z)))
  refine (denseRange_sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).induction_on z ?_ ?_
  · exact isClosed_eq (B.continuous.comp J.continuous)
      (J.continuous.comp (Z.continuous.comp (C.continuous.comp Z.symm.continuous)))
  · intro u
    change B (J (I u)) = J (Z (C (Z.symm (I u))))
    have hB : B (K u) = K (A u) :=
      nativeNegativeHalfSmoothMulL_inclusion hF hO hD τ0 m hM hm hg u
    have hA : I (A u) = Z (C (Z.symm (I u))) :=
      sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg u
    exact (congrArg B (htrans u)).trans
      (hB.trans ((htrans (A u)).symm.trans (congrArg J hA)))

theorem nativeNegativeHalfSmoothMulL_L2_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (v : SphereL2) :
    nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v)) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (sphereContinuousScalarMulL (smoothSphereValue m) v)) := by
  rw [nativeNegativeHalfSmoothMulL_zero_inclusion,LinearIsometryEquiv.symm_apply_apply]

end OAI.AnisotropicCalderon.NativeNegativeHalfSmoothMultiplier
