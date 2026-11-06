import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SphereSobolevOrderOneRotationPairing
import Calderon.SphereContinuousScalarMultiplierSymmetry

set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction
open EnergyBridge DirichletFamily SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier

def nativeZeroCoefficientMulL (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : SmoothCoefficientJets 3) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))).comp
      (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma nativeZeroCoefficientMulL_zeroEquiv_symm_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : SmoothCoefficientJets 3) (u : SphereSobolev 0) :
    (sphereSobolevZeroEquiv hO hD).symm (nativeZeroCoefficientMulL hO hD F u) =
      sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
        ((sphereSobolevZeroEquiv hO hD).symm u) :=
  LinearIsometryEquiv.symm_apply_apply (sphereSobolevZeroEquiv hO hD) _

def nativeOrderOneScalarRotationL (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (F : SmoothCoefficientJets 3) (i j : Fin 3) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (nativeZeroCoefficientMulL hO hD F).comp (sphereSobolevRotationL 1 i j)

def nativeOrderOneScalarRotationAdjointL (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2) (i j : Fin 3) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  -((sphereSobolevRotationL 1 i j).comp
    (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hCoeff))

lemma inner_nativeOrderOneScalarRotation_adjoint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2) (i j : Fin 3)
    (u v : SphereSobolev 1) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm (nativeOrderOneScalarRotationL hO hD F3 i j u),
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) v)⟫_ℝ =
    ⟪(sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv hO hD).symm
        (nativeOrderOneScalarRotationAdjointL hcalc hF hO hD τ0 F3 F2 hCoeff i j v)⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let R : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevRotationL 1 i j
  let M := nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hCoeff
  let C := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
  have hM : Z.symm (I (M v)) = C (Z.symm (I v)) :=
    (congrArg Z.symm (sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero
      hcalc hF hO hD τ0 F3 F2 hCoeff v)).trans (Z.symm_apply_apply _)
  have hLeft : Z.symm (nativeOrderOneScalarRotationL hO hD F3 i j u) = C (Z.symm (R u)) :=
    nativeZeroCoefficientMulL_zeroEquiv_symm_apply hO hD F3 (R u)
  have hSym := inner_sphereContinuousScalarMulL_left
    (smoothSphereValue (nativeH2CoefficientSmoothData F3)) (Z.symm (R u)) (Z.symm (I v))
  have hSkew := inner_sphereSobolevRotationL_one_zeroEquiv_skew hO hD i j u (M v)
  have hRight : Z.symm
      (nativeOrderOneScalarRotationAdjointL hcalc hF hO hD τ0 F3 F2 hCoeff i j v) =
      -(Z.symm (R (M v))) := Z.symm.map_neg _
  exact (congrArg (fun x : SphereL2 => ⟪x,Z.symm (I v)⟫_ℝ) hLeft).trans
    (hSym.trans ((congrArg (fun x : SphereL2 => ⟪Z.symm (R u),x⟫_ℝ) hM.symm).trans
      (hSkew.trans ((inner_neg_right (Z.symm (I u)) (Z.symm (R (M v)))).symm.trans
        (congrArg (fun x : SphereL2 => ⟪Z.symm (I u),x⟫_ℝ) hRight.symm)))))

end OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction
#print axioms OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction.nativeZeroCoefficientMulL
#print axioms OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction.nativeZeroCoefficientMulL_zeroEquiv_symm_apply
#print axioms OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction.nativeOrderOneScalarRotationL
#print axioms OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction.nativeOrderOneScalarRotationAdjointL
#print axioms OAI.AnisotropicCalderon.NativeOrderOneScalarRotationAdjunction.inner_nativeOrderOneScalarRotation_adjoint
