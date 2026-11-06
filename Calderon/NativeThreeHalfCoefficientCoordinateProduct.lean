import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeBoundaryCoefficientL2Decomposition

/-! The coordinate is multiplied by the coefficient before extension. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

def coefficientCoordinateJets (F : SmoothCoefficientJets 3) (j : Fin 3) : SmoothCoefficientJets 3 :=
  compactCoefficient 3 (fun x : R3 => x j * coefficientValue 3 F x)
    ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.mul (contDiff_coefficientValue 3 F))
    (hasCompactSupport_coefficientValue 3 F).mul_left

lemma coefficientValue_coordinateJets (F : SmoothCoefficientJets 3) (j : Fin 3) :
    coefficientValue 3 (coefficientCoordinateJets F j) = fun x => x j * coefficientValue 3 F x :=
  coefficientValue_compactCoefficient 3 _ _ _

attribute [local irreducible] nativeThreeHalfCoefficientMulL sphereSobolevLinearCoordinateMulL
  sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma nativeThreeHalfCoefficientMulL_coordinate_comp_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 3) (j : Fin 3)
    (hSphere : ∀ x : UnitSphere, coefficientValue 3 G x.val = x.val j * coefficientValue 3 F x.val) :
    (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F) =
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let MF := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let CF := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
  let CX := sphereContinuousScalarMulL (sphereCoordinate j)
  let CG := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData G))
  have hFgraph : I (MF f) = Z (CF (Z.symm (I f))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F f
  have hCoordinate : I
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) (MF f)) =
      Z (CX (CF (Z.symm (I f)))) := by
    have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (3/2 : ℝ)
      (by norm_num) (EuclideanSpace.single j 1) (MF f) (CF (Z.symm (I f))) hFgraph
    simpa only [sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL] using h
  have hScalar : sphereCoordinate j * smoothSphereValue (nativeH2CoefficientSmoothData F) =
      smoothSphereValue (nativeH2CoefficientSmoothData G) := by
    apply ContinuousMap.ext
    intro x
    exact (hSphere x).symm
  have hProduct : CX (CF (Z.symm (I f))) = CG (Z.symm (I f)) :=
    (sphereContinuousScalarMulL_mul_apply (sphereCoordinate j)
      (smoothSphereValue (nativeH2CoefficientSmoothData F)) (Z.symm (I f))).trans
      (congrArg (fun m : C(UnitSphere,ℝ) => sphereContinuousScalarMulL m (Z.symm (I f))) hScalar)
  exact hCoordinate.trans ((congrArg Z hProduct).trans
    (sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 G f).symm)

lemma nativeThreeHalfCoefficientMulL_coordinateJets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3) (j : Fin 3) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (coefficientCoordinateJets F j) =
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F) :=
  (nativeThreeHalfCoefficientMulL_coordinate_comp_eq hcalc hF hO hD τ0 F
    (coefficientCoordinateJets F j) j (fun x => congrFun (coefficientValue_coordinateJets F j) x.val)).symm

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.coefficientCoordinateJets
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.coefficientValue_coordinateJets
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_coordinate_comp_eq
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_coordinateJets
