import Calderon.NativeH2ThreeHalfValueTrace
import Calderon.NativeFullSharpHalfTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-NATIVE-HALF-TEST-DENSITY-EXPANSION-v001.md. Exact old physical core in native high/half completion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError NativeH2ThreeHalfValueTrace
  NativeFullSharpHalfTrace NativeSmoothSharpTraceCompletion

theorem sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SmoothData) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 f)) =
    smoothHalfTrace hF hO hD τ0 f := by
  have hHighHalf := sphereSobolevInclusionL_nativeThreeHalfValueTraceL
    hcalc hF hO hD τ0 (smoothBallSobolev 2 f)
  have hFirst := congrArg (nativeHalfTraceL hF hO hD τ0) (firstOrder_smoothBallSobolev 1 f)
  exact hHighHalf.trans (hFirst.trans (nativeHalfTraceL_smoothSobolev hF hO hD τ0 f))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
