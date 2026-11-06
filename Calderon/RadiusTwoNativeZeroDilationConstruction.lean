import Calderon.RadiusTwoNativeTestDilationBound

/-! Full EXPANSION.json precedes this focused partition of original nativezero dilation5. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal Distributions ContDiff Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

def radiusTwoNativeZeroDilation : RadiusTwoH1Zero →L[ℝ] BallH1Zero :=
  ((nativeZeroTestLinear ballOpens).comp radiusTwoTestPullbackLinear).extendOfNorm
    (nativeZeroTestLinear radiusTwoOpens)

theorem radiusTwoNativeZeroDilation_test (phi : 𝓓(radiusTwoOpens, ℝ)) :
    radiusTwoNativeZeroDilation (nativeZeroTestLinear radiusTwoOpens phi) =
      nativeZeroTestLinear ballOpens (radiusTwoTestPullback phi) :=
  LinearMap.extendOfNorm_eq (denseRange_nativeZeroTestLinear radiusTwoOpens)
    ⟨3,norm_nativeZeroTestPullback_le_three⟩ phi

theorem norm_radiusTwoNativeZeroDilation_le_three : ‖radiusTwoNativeZeroDilation‖ ≤ 3 :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_nativeZeroTestLinear radiusTwoOpens)
    (by norm_num) norm_nativeZeroTestPullback_le_three

end OAI.AnisotropicCalderon.ExteriorSource
