import Calderon.NativeCoefficientRotationFieldSkew
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-HIGH-ROTATION-MULTIPLIER-GAIN-EXPANSION-v001.md. Same-order multiplier realization of the actual field commutator. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def nativeThreeHalfRotationFieldCommutatorGainL
    (F H : Fin 3 → Fin 3 → SmoothCoefficientJets 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (F i j)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (H i j))

attribute [local irreducible] sphereSobolevInclusionL nativeCoefficientRotationFieldL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

lemma nativeThreeHalfRotationFieldCommutatorGainL_inclusion
    (F3 H3 : Fin 3 → Fin 3 → SmoothCoefficientJets 3)
    (F2 H2 : Fin 3 → Fin 3 → SmoothCoefficientJets 2) (Q2 : SmoothCoefficientJets 2)
    (hFValue : ∀ i j, coefficientValue 3 (F3 i j) = coefficientValue 2 (F2 i j))
    (hHValue : ∀ i j, coefficientValue 3 (H3 i j) = coefficientValue 2 (H2 i j))
    (hDerivative : ∀ i j (x : UnitSphere), coefficientValue 2 (H2 i j) x.val =
      SmoothSphereRotation.sphereRotationDerivative j i (coefficientValue 2 Q2) x.val)
    (f : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfRotationFieldCommutatorGainL hcalc hF hO hD τ0 F3 H3 f)) =
    nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F2
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) -
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2
      (nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F2
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f)) := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let MH (Q : SmoothCoefficientJets 3) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML (Q : SmoothCoefficientJets 2) := nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let MN (Q : SmoothCoefficientJets 2) := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let V := nativeCoefficientRotationFieldL hcalc hF hO hD τ0 F2
  have hCompatible (P3 : SmoothCoefficientJets 3) (P2 : SmoothCoefficientJets 2)
      (hP : coefficientValue 3 P3 = coefficientValue 2 P2) (v : SphereSobolev (3/2 : ℝ)) :
      J (I (MH P3 v)) = MN P2 (J (I v)) := by
    have hHigh : I (MH P3 v) = ML P2 (I v) :=
      congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
        (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 P3 P2 hP)
    have hHalf : J (ML P2 (I v)) = MN P2 (J (I v)) :=
      congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I v))
        (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 P2)
    exact (congrArg J hHigh).trans hHalf
  have hTerm (i j : Fin 3) : J (I (MH (F3 i j) (MH (H3 i j) f))) =
      MN (F2 i j) (MN (H2 i j) (J (I f))) :=
    (hCompatible (F3 i j) (F2 i j) (hFValue i j) (MH (H3 i j) f)).trans
      (congrArg (MN (F2 i j)) (hCompatible (H3 i j) (H2 i j) (hHValue i j) f))
  have hSum : J (I (nativeThreeHalfRotationFieldCommutatorGainL hcalc hF hO hD τ0 F3 H3 f)) =
      ∑ i : Fin 3, ∑ j : Fin 3, MN (F2 i j) (MN (H2 i j) (J (I f))) := by
    unfold nativeThreeHalfRotationFieldCommutatorGainL
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
    exact Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hTerm i j))
  have hLow : V (ML Q2 (I f)) - MN Q2 (V (I f)) =
      ∑ i : Fin 3, ∑ j : Fin 3, MN (F2 i j) (MN (H2 i j) (J (I f))) := by
    have h := congrArg
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (I f))
      (nativeCoefficientRotationField_commutator_nativeMultiplier
        hcalc hF hO hD τ0 F2 Q2 H2 hDerivative)
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply,V,ML,MN,J] using h
  exact hSum.trans hLow.symm

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeThreeHalfRotationFieldCommutatorGainL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeThreeHalfRotationFieldCommutatorGainL_inclusion
