import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.SphereSobolevSameOrderMidpoint

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeHalfSmoothMultiplier

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
  (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
  (hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2)

include hCoeff

lemma sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue
    (f : SphereSobolev (1/2:ℝ)) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2 f) =
      sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
          ((sphereSobolevZeroEquiv hO hD).symm
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) f))) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F2)
  have hMul := nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F2 hM hm hg
  have hPoint := congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (A f)) hMul
  have hSphere : smoothSphereValue (coefficientSmoothData F2) =
      smoothSphereValue (nativeH2CoefficientSmoothData F3) := by
    ext x
    exact congrFun hCoeff.symm (x : R3)
  exact hPoint.trans ((sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0
    (coefficientSmoothData F2) hM hm hg f).trans
    (congrArg (fun m => sphereSobolevZeroEquiv hO hD
      (sphereContinuousScalarMulL m ((sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) f)))) hSphere))

lemma nativeCoefficientMulL_high_half_compatibility :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3) =
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  have hTrans := sphereSobolevInclusionL_trans (3/2:ℝ) (1/2:ℝ) 0 (by norm_num) (by norm_num)
  have hOut := congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 =>
    I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3 f)) hTrans
  have hIn := congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => I f) hTrans
  have hHigh := sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F3 f
  have hLow := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0
    F3 F2 hCoeff (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  have hValue := congrArg (fun x : SphereSobolev 0 => sphereSobolevZeroEquiv hO hD
    (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
      ((sphereSobolevZeroEquiv hO hD).symm x))) hIn
  exact hOut.trans (hHigh.trans (hValue.symm.trans hLow.symm))

def nativeOrderOneCoefficientMulL : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  sphereSobolevSameOrderMidpointL
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2)
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 F3 F2 hCoeff)

lemma sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero (f : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num)
      (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hCoeff f) =
      sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
          ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) f))) := by
  let M := nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hCoeff
  have hLower : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (M f) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) f) :=
    congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
      (sphereSobolevSameOrderMidpointL_lower_inclusion
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2)
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3)
        (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 F3 F2 hCoeff))
  have hTrans := sphereSobolevInclusionL_trans 1 (1/2:ℝ) 0 (by norm_num) (by norm_num)
  have hOut := congrArg (fun I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => I (M f)) hTrans
  have hIn := congrArg (fun I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => I f) hTrans
  have hCoarse := congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hLower
  have hLow := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0
    F3 F2 hCoeff (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) f)
  have hValue := congrArg (fun x : SphereSobolev 0 => sphereSobolevZeroEquiv hO hD
    (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
      ((sphereSobolevZeroEquiv hO hD).symm x))) hIn
  exact hOut.symm.trans (hCoarse.trans (hLow.trans hValue))

end OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.nativeCoefficientMulL_high_half_compatibility
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.nativeOrderOneCoefficientMulL
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier.sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero
