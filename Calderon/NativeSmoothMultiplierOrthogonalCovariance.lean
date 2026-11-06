import Calderon.NativeSmoothMultiplicationTrace
import Calderon.NativeHarmonicFirstOrderOrthogonalPullback
import Calderon.NativeHalfTraceOrthogonalPullback
import Calderon.NativeHalfSmoothMultiplier

/-! Expanded first in EXPANSION-native-scalar-multiplier-orthogonal-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
  NativeFullSharpHalfTrace NativeHalfSmoothMultiplier

variable (e : R3 ≃ₗᵢ[ℝ] R3) (m : SmoothData) {M N : ℝ}
  (hM : 0 ≤ M) (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
  (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
  (hN : 0 ≤ N)
  (hn : ∀ x ∈ (ballOpens : Set R3), |(orthogonalSmoothPullback e m).1 x| ≤ N)
  (hgn : ∀ x ∈ (ballOpens : Set R3), ‖gradient (orthogonalSmoothPullback e m).1 x‖ ≤ N)

lemma nativeH1OrthogonalPullback_contDiffSMulL (u : BallH1) :
    nativeH1OrthogonalPullback e
      (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) m.1 m.2 hM hm hg u) =
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (orthogonalSmoothPullback e m).1 (orthogonalSmoothPullback e m).2 hN hn hgn
      (nativeH1OrthogonalPullback e u) := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
  let Q : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (orthogonalSmoothPullback e m).1 (orthogonalSmoothPullback e m).2 hN hn hgn
  change nativeH1OrthogonalPullback e (S u) = Q (nativeH1OrthogonalPullback e u)
  refine denseRange_smoothSobolev.induction_on u
    (isClosed_eq ((nativeH1OrthogonalPullback e).continuous.comp S.continuous)
      (Q.continuous.comp (nativeH1OrthogonalPullback e).continuous)) ?_
  intro f
  change nativeH1OrthogonalPullback e (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg (smoothSobolev f)) =
    TauCeti.W1p.contDiffSMulL (orthogonalSmoothPullback e m).1
      (orthogonalSmoothPullback e m).2 hN hn hgn (nativeH1OrthogonalPullback e (smoothSobolev f))
  rw [contDiffSMulL_smoothSobolev,nativeH1OrthogonalPullback_smoothSobolev,
    nativeH1OrthogonalPullback_smoothSobolev,contDiffSMulL_smoothSobolev]
  apply congrArg smoothSobolev
  apply Subtype.ext
  rfl

lemma nativeHalfSmoothMulL_orthogonal_covariance
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SphereSobolev (1/2:ℝ)) :
    nativeHalfSmoothMulL hF hO hD τ0 (orthogonalSmoothPullback e m) hN hn hgn
      (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f) =
    sphereSobolevOrthogonalPullbackL (1/2:ℝ) e
      (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg f) := by
  change nativeHalfTraceL hF hO hD τ0
      (TauCeti.W1p.contDiffSMulL (orthogonalSmoothPullback e m).1
        (orthogonalSmoothPullback e m).2 hN hn hgn
        (harmonicFirstOrderLiftCompletion hF (sphereSobolevOrthogonalPullbackL (1/2:ℝ) e f))) = _
  rw [← harmonicFirstOrderLiftCompletion_orthogonalPullback hF hO e,
    ← nativeH1OrthogonalPullback_contDiffSMulL e m hM hm hg hN hn hgn,
    nativeHalfTraceL_nativeH1OrthogonalPullback]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_contDiffSMulL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfSmoothMulL_orthogonal_covariance
