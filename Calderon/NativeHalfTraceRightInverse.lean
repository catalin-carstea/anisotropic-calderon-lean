import Calderon.NativeFullSharpHalfTrace
import Calderon.NativeHarmonicH1LiftTraceCompatibility

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.NativeHalfTraceRightInverse
open NativeFullSharpHalfTrace NativeHarmonicH1LiftCompletion
  NativeHarmonicH1LiftTraceCompatibility SphereHarmonic SpectralCoreRegularity DirichletFamily

theorem nativeHalfTraceL_harmonicFirstOrderLiftCompletion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (f : SphereSobolev (1/2 : ℝ)) :
    nativeHalfTraceL hF hO hD τ0 (harmonicFirstOrderLiftCompletion hF f) = f := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_nativeHalfTraceL]
  exact sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion
    hF hO hD τ0 k f

theorem nativeHalfTraceL_comp_harmonicFirstOrderLiftCompletion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    (nativeHalfTraceL hF hO hD τ0).comp (harmonicFirstOrderLiftCompletion hF) =
      ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  exact nativeHalfTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 f

end OAI.AnisotropicCalderon.NativeHalfTraceRightInverse
