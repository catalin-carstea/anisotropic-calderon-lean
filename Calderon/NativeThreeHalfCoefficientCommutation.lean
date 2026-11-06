import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeCoefficientRotationProductRule

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-HIGH-ROTATION-MULTIPLIER-GAIN-EXPANSION-v001.md. Same scalar-value graph on all H3half. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily SphereHarmonic

attribute [local irreducible] nativeThreeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevZeroEquiv sphereContinuousScalarMulL

lemma nativeThreeHalfCoefficientMulL_comm_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 3) (u : SphereSobolev (3/2 : ℝ)) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G u) =
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F u) := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M (Q : SmoothCoefficientJets 3) : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let C (Q : SmoothCoefficientJets 3) : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let v : SphereL2 := Z.symm (I u)
  have hValue (Q : SmoothCoefficientJets 3) (w : SphereSobolev (3/2 : ℝ)) :
      I (M Q w) = Z (C Q (Z.symm (I w))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 Q w
  have hPair (Q K : SmoothCoefficientJets 3) :
      I (M Q (M K u)) = Z (C Q (C K v)) :=
    (hValue Q (M K u)).trans
      ((congrArg (fun z : SphereSobolev 0 => Z (C Q (Z.symm z))) (hValue K u)).trans
        (congrArg (fun w : SphereL2 => Z (C Q w)) (Z.symm_apply_apply (C K v))))
  have hComm : C F (C G v) = C G (C F v) :=
    DirichletFamily.DriftBootstrap.sphereContinuousScalarMulL_comm_apply
      (smoothSphereValue (nativeH2CoefficientSmoothData F))
      (smoothSphereValue (nativeH2CoefficientSmoothData G)) v
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  exact (hPair F G).trans ((congrArg Z hComm).trans (hPair G F).symm)

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_comm_apply
