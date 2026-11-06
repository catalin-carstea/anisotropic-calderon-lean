import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeSmoothOperatorRealization

/-! Same actual native product at H3/2. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace

attribute [local irreducible] nativeThreeHalfValueTraceL nativeThreeHalfCoefficientMulL
  coefficientMultiplier smoothBallSobolev

lemma nativeThreeHalfValueTraceL_coefficientMultiplier
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Q : SmoothCoefficientJets 3) (U : BallSobolev 2) :
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (coefficientMultiplier hcalc 2 Q U) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U) := by
  let Z := sphereSobolevZeroEquiv hO hD
  let C := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  have hU : I (T U) = Z (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)) :=
    sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero hcalc hF hO hD τ0 U
  have hRecover : Z.symm (I (T U)) = τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U) :=
    (congrArg Z.symm hU).trans (Z.symm_apply_apply _)
  have hLeft : I (T (coefficientMultiplier hcalc 2 Q U)) =
      Z (C (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U))) :=
    (sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero hcalc hF hO hD τ0 _).trans
      (congrArg Z (valueTraceL_firstOrder_H2CoefficientMultiplier hcalc τ0 Q U))
  have hRight : I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q (T U)) =
      Z (C (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U))) :=
    (sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 Q (T U)).trans
      (congrArg (fun v : SphereL2 => Z (C v)) hRecover)
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  exact hLeft.trans hRight.symm

lemma nativeThreeHalfValueTraceL_smooth_coefficientProductData
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Q : SmoothCoefficientJets 3) (v : SmoothData) :
    nativeThreeHalfValueTraceL hcalc hF hO hD τ0
      (smoothBallSobolev 2 (coefficientProductData 2 Q v)) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 v)) :=
  (congrArg (nativeThreeHalfValueTraceL hcalc hF hO hD τ0)
    (coefficientMultiplier_smoothBallSobolev hcalc 2 Q v).symm).trans
      (nativeThreeHalfValueTraceL_coefficientMultiplier hcalc hF hO hD τ0 Q (smoothBallSobolev 2 v))

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfValueTraceL_coefficientMultiplier
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfValueTraceL_smooth_coefficientProductData
