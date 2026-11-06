import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.NativeCoefficientRotationProductRule
import Calderon.NativeSmoothMultiplierCommonSupportJets
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open EnergyBridge DirichletFamily SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier DirichletFamily.DriftBootstrap
attribute [local irreducible] nativeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevZeroEquiv sphereContinuousScalarMulL
lemma nativeHalfCoefficientMulL_lowerJets_comm_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 3) (u : SphereSobolev (1/2 : ℝ)) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets F)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets G) u) =
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets G)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets F) u) := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M (Q : SmoothCoefficientJets 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let C (Q : SmoothCoefficientJets 3) : SphereL2 →L[ℝ] SphereL2 :=
    sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let v : SphereL2 := Z.symm (I u)
  have hValue (Q : SmoothCoefficientJets 3) (w : SphereSobolev (1/2 : ℝ)) :
      I (M Q w) = Z (C Q (Z.symm (I w))) :=
    sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0 Q (smoothMultiplierLowerJets Q) rfl w
  have hPair (Q K : SmoothCoefficientJets 3) :
      I (M Q (M K u)) = Z (C Q (C K v)) :=
    (hValue Q (M K u)).trans
      ((congrArg (fun z : SphereSobolev 0 => Z (C Q (Z.symm z))) (hValue K u)).trans
        (congrArg (fun w : SphereL2 => Z (C Q w)) (Z.symm_apply_apply (C K v))))
  have hComm : C F (C G v) = C G (C F v) :=
    DirichletFamily.DriftBootstrap.sphereContinuousScalarMulL_comm_apply
      (smoothSphereValue (nativeH2CoefficientSmoothData F))
      (smoothSphereValue (nativeH2CoefficientSmoothData G)) v
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact (hPair F G).trans ((congrArg Z hComm).trans (hPair G F).symm)

end OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
