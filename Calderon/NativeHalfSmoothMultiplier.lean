import Calderon.NativeHalfTraceRightInverse
import Calderon.NativeSmoothMultiplicationTrace

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeHalfSmoothMultiplier
open EnergyBridge DirichletFamily SphereHarmonic SpectralCoreRegularity
  NativeFullSharpHalfTrace NativeHarmonicH1LiftCompletion NativeHalfTraceRightInverse

def nativeHalfSmoothMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (nativeHalfTraceL hF hO hD τ0).comp
    ((TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) m.1 m.2 hM hm hg).comp (harmonicFirstOrderLiftCompletion hF))

theorem norm_nativeHalfSmoothMulL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    ‖nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg‖ ≤
      ‖nativeHalfTraceL hF hO hD τ0‖ * ((2*M) * ‖harmonicFirstOrderLiftCompletion hF‖) := by
  let T := nativeHalfTraceL hF hO hD τ0
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
  let P := harmonicFirstOrderLiftCompletion hF
  change ‖T.comp (S.comp P)‖ ≤ ‖T‖ * ((2*M)*‖P‖)
  calc
    ‖T.comp (S.comp P)‖ ≤ ‖T‖ * ‖S.comp P‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * (‖S‖*‖P‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg T)
    _ ≤ ‖T‖ * ((2*M)*‖P‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (TauCeti.W1p.norm_contDiffSMulL_le m.2 hM hm hg)
          (norm_nonneg P)) (norm_nonneg T)

theorem sphereSobolevInclusionL_nativeHalfSmoothMulL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (f : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) =
    sphereSobolevZeroEquiv hO hD (sphereContinuousScalarMulL (smoothSphereValue m)
      ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f))) := by
  have hLift : sphereSobolevZeroEquiv hO hD
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)) =
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f := by
    rw [← sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0,
      nativeHalfTraceL_harmonicFirstOrderLiftCompletion]
  have hLift' : τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f) =
      (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) f) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      congrArg (sphereSobolevZeroEquiv hO hD).symm hLift
  change sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
    (nativeHalfTraceL hF hO hD τ0
      (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
        (harmonicFirstOrderLiftCompletion hF f))) = _
  rw [sphereSobolevInclusionL_nativeHalfTraceL,valueTraceL_contDiffSMulL,hLift']

theorem nativeHalfSmoothMulL_eq_of_sphereValue_eq
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m n : SmoothData) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hgm : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (hn : ∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N)
    (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N)
    (hSphere : smoothSphereValue m = smoothSphereValue n) :
    nativeHalfSmoothMulL hF hO hD τ0 m hM hm hgm =
      nativeHalfSmoothMulL hF hO hD τ0 n hN hn hgn := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  rw [sphereSobolevInclusionL_nativeHalfSmoothMulL,
    sphereSobolevInclusionL_nativeHalfSmoothMulL,hSphere]

end OAI.AnisotropicCalderon.NativeHalfSmoothMultiplier
