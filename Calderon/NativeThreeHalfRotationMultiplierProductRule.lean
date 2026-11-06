import Calderon.NativeCoefficientRotationProductRule
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-HIGH-ROTATION-MULTIPLIER-GAIN-EXPANSION-v001.md. Literal compatible rotation product rule. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevRotationL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

lemma sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 G3 : SmoothCoefficientJets 3) (F2 G2 : SmoothCoefficientJets 2)
    (hFValue : coefficientValue 3 F3 = coefficientValue 2 F2)
    (hGValue : coefficientValue 3 G3 = coefficientValue 2 G2) (i j : Fin 3)
    (hDerivative : ∀ x : UnitSphere, coefficientValue 2 G2 x.val =
      SmoothSphereRotation.sphereRotationDerivative i j (coefficientValue 2 F2) x.val) :
    (sphereSobolevRotationL (3/2 : ℝ) i j).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3) =
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2).comp
      (sphereSobolevRotationL (3/2 : ℝ) i j) +
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G3) := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let RH : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevRotationL (3/2 : ℝ) i j
  let RL : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevRotationL (1/2 : ℝ) i j
  let MH (Q : SmoothCoefficientJets 3) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML (Q : SmoothCoefficientJets 2) := nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let MN (Q : SmoothCoefficientJets 2) := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  have hRot (v : SphereSobolev (3/2 : ℝ)) : J (RH v) = RL (I v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (sphereSobolevRotationL_threehalf_half_compatibility i j)
  have hHigh (P3 : SmoothCoefficientJets 3) (P2 : SmoothCoefficientJets 2)
      (hP : coefficientValue 3 P3 = coefficientValue 2 P2) (v : SphereSobolev (3/2 : ℝ)) :
      I (MH P3 v) = ML P2 (I v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 P3 P2 hP)
  have hHalf (P : SmoothCoefficientJets 2) (v : SphereSobolev (1/2 : ℝ)) :
      J (ML P v) = MN P (J v) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 P)
  apply ContinuousLinearMap.ext
  intro f
  change RH (MH F3 f) = ML F2 (RH f) + I (MH G3 f)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hLow : RL (ML F2 (I f)) = MN F2 (RL (I f)) + MN G2 (J (I f)) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I f))
      (sphereSobolevRotationL_nativeCoefficient_product_rule hcalc hF hO hD τ0 F2 G2 i j hDerivative)
  have hLeft : J (RH (MH F3 f)) = MN F2 (RL (I f)) + MN G2 (J (I f)) :=
    (hRot (MH F3 f)).trans ((congrArg RL (hHigh F3 F2 hFValue f)).trans hLow)
  have hFirst : J (ML F2 (RH f)) = MN F2 (RL (I f)) :=
    (hHalf F2 (RH f)).trans (congrArg (MN F2) (hRot f))
  have hSecond : J (I (MH G3 f)) = MN G2 (J (I f)) :=
    (congrArg J (hHigh G3 G2 hGValue f)).trans (hHalf G2 (I f))
  have hRight : J (ML F2 (RH f) + I (MH G3 f)) =
      MN F2 (RL (I f)) + MN G2 (J (I f)) :=
    (J.map_add _ _).trans (congrArg₂
      (fun x y : SphereSobolev (-(1/2 : ℝ)) => x+y) hFirst hSecond)
  exact hLeft.trans hRight.symm

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_nativeThreeHalfCoefficient_product_rule
