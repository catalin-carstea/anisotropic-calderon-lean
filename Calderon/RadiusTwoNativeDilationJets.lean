import Calderon.RadiusTwoNativeTestValueDilation
import Calderon.RadiusTwoNativeTestGradientDilation

/-! Full EXPANSION.json precedes the actual native dilation jet identities. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal Distributions Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem value_radiusTwoNativeZeroDilation (w : RadiusTwoH1Zero) :
    TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (w : RadiusTwoH1)) := by
  let L : RadiusTwoH1Zero →L[ℝ] BallSobolev 0 :=
    (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).comp
      radiusTwoNativeZeroDilation
  let R : RadiusTwoH1Zero →L[ℝ] BallSobolev 0 :=
    (radiusTwoNativeL2Dilation (V := ℝ)).comp
      (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2))
  have htest (phi : 𝓓(radiusTwoOpens, ℝ)) : L (nativeZeroTestLinear radiusTwoOpens phi) =
      R (nativeZeroTestLinear radiusTwoOpens phi) := by
    change TauCeti.W1p.value (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens phi) : BallH1) =
        radiusTwoNativeL2Dilation (TauCeti.W1p.value
          (nativeZeroTestLinear radiusTwoOpens phi : RadiusTwoH1))
    exact value_radiusTwoNativeZeroDilation_test phi
  exact (denseRange_nativeZeroTestLinear radiusTwoOpens).induction_on w
    (isClosed_eq L.continuous R.continuous) htest

theorem gradient_radiusTwoNativeZeroDilation (w : RadiusTwoH1Zero) :
    TauCeti.W1p.gradient (radiusTwoNativeZeroDilation w : BallH1) =
      (2 : ℝ) • radiusTwoNativeL2Dilation (TauCeti.W1p.gradient (w : RadiusTwoH1)) := by
  let V1 : BallH1Zero →L[ℝ] Lp R3 2 ((volume : Measure R3).restrict ballOpens) :=
    (TauCeti.W1p.gradientL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).comp
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  let V2 : RadiusTwoH1Zero →L[ℝ] Lp R3 2 ((volume : Measure R3).restrict radiusTwoOpens) :=
    (TauCeti.W1p.gradientL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2)).comp
      (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule.subtypeL
  let L : RadiusTwoH1Zero →L[ℝ] Lp R3 2 ((volume : Measure R3).restrict ballOpens) :=
    V1.comp radiusTwoNativeZeroDilation
  let R : RadiusTwoH1Zero →L[ℝ] Lp R3 2 ((volume : Measure R3).restrict ballOpens) :=
    (2 : ℝ) • ((radiusTwoNativeL2Dilation (V := R3)).comp V2)
  have htest (phi : 𝓓(radiusTwoOpens, ℝ)) : L (nativeZeroTestLinear radiusTwoOpens phi) =
      R (nativeZeroTestLinear radiusTwoOpens phi) := by
    change TauCeti.W1p.gradient (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens phi) : BallH1) =
        (2 : ℝ) • radiusTwoNativeL2Dilation (TauCeti.W1p.gradient
          (nativeZeroTestLinear radiusTwoOpens phi : RadiusTwoH1))
    exact gradient_radiusTwoNativeZeroDilation_test phi
  exact (denseRange_nativeZeroTestLinear radiusTwoOpens).induction_on w
    (isClosed_eq L.continuous R.continuous) htest

end OAI.AnisotropicCalderon.ExteriorSource
