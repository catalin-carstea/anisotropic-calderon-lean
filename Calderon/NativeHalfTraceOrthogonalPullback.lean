import Calderon.SphereSobolevZeroOrthogonalPullback
import Calderon.NativeH1OrthogonalValueTrace
import Calderon.NativeFullSharpHalfTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace

/-! The same `tau0` on the native H1 domain, with no H2 density assumption. -/

lemma nativeHalfTraceL_nativeH1OrthogonalPullback
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    nativeHalfTraceL hF hO hD τ0 (nativeH1OrthogonalPullback e u) =
      sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e (nativeHalfTraceL hF hO hD τ0 u) := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  have hIncl := congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 =>
      A (nativeHalfTraceL hF hO hD τ0 u))
    (sphereSobolevInclusionL_orthogonalPullback (1/2 : ℝ) 0 (by norm_num) e)
  calc
    _ = sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (nativeH1OrthogonalPullback e u)) :=
      sphereSobolevInclusionL_nativeHalfTraceL hF hO hD τ0 _
    _ = sphereSobolevZeroEquiv hO hD (sphereL2OrthogonalPullback e (τ0.valueTraceL u)) := by
      rw [valueTraceL_nativeH1OrthogonalPullback]
    _ = sphereSobolevOrthogonalPullbackL 0 e (sphereSobolevZeroEquiv hO hD (τ0.valueTraceL u)) :=
      sphereSobolevZeroEquiv_orthogonalPullback hO hD e _
    _ = sphereSobolevOrthogonalPullbackL 0 e
        (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (nativeHalfTraceL hF hO hD τ0 u)) := by
      rw [sphereSobolevInclusionL_nativeHalfTraceL]
    _ = _ := hIncl.symm

lemma sphereSobolevCoefficientL_nativeHalfTrace_orthogonalPullback
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (e : R3 ≃ₗᵢ[ℝ] R3)
    (u : BallH1) (k : ℕ) :
    sphereSobolevCoefficientL (1/2 : ℝ) k
      (nativeHalfTraceL hF hO hD τ0 (nativeH1OrthogonalPullback e u)) =
      harmonicSphereOrthogonalPullback e k
        (sphereSobolevCoefficientL (1/2 : ℝ) k (nativeHalfTraceL hF hO hD τ0 u)) := by
  rw [nativeHalfTraceL_nativeH1OrthogonalPullback,sphereSobolevCoefficientL_orthogonalPullback]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_nativeH1OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevCoefficientL_nativeHalfTrace_orthogonalPullback
