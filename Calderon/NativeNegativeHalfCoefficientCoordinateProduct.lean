import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.NativeNegativeHalfMultiplierL2Inclusion
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.NativeBoundaryCoefficientL2Decomposition
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeNegativeHalfCoefficientCoordinateProduct
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeNegativeHalfSmoothMultiplier

lemma nativeNegativeHalfCoefficientMulL_zero_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (z : SphereSobolev 0) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) z) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F))
          ((sphereSobolevZeroEquiv hO hD).symm z))) := by
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  have hEq := nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hgm
  exact (congrArg (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) z)) hEq).trans
    (nativeNegativeHalfSmoothMulL_zero_inclusion hF hO hD τ0 (coefficientSmoothData F) hM hm hgm z)

lemma nativeNegativeHalfCoefficientMulL_coordinate_comp_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 2) (j : Fin 3)
    (hSphere : smoothSphereValue (coefficientSmoothData G) =
      smoothSphereValue (coefficientSmoothData F) * sphereCoordinate j) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) (EuclideanSpace.single j 1)) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  let A := (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2:ℝ)) (EuclideanSpace.single j 1))
  let B := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let X0 := sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1)
  let CF := sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F))
  let CX := sphereContinuousScalarMulL (sphereCoordinate j)
  let CG := sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData G))
  have hProduct (v : SphereL2) : CF (CX v) = CG v :=
    (sphereContinuousScalarMulL_mul_apply (smoothSphereValue (coefficientSmoothData F))
      (sphereCoordinate j) v).trans
      (congrArg (fun m : C(UnitSphere,ℝ) => sphereContinuousScalarMulL m v) hSphere.symm)
  have hPoint (z : SphereSobolev 0) : A (J z) = B (J z) := by
    have hX := (sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-(1/2:ℝ))
      (by norm_num) (EuclideanSpace.single j 1) z).symm
    have hCoord : X0 z = Z (CX (Z.symm z)) := by
      have he := sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD
        (EuclideanSpace.single j 1) (Z.symm z)
      simp only [sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL] at he
      exact (congrArg X0 (Z.apply_symm_apply z).symm).trans he
    have hLeft := (congrArg (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F) hX).trans
      (nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 F (X0 z))
    have hSub := congrArg (fun y : SphereSobolev 0 => J (Z (CF (Z.symm y)))) hCoord
    have hCancel := congrArg (fun v : SphereL2 => J (Z (CF v))) (Z.symm_apply_apply (CX (Z.symm z)))
    have hProd := congrArg (fun v : SphereL2 => J (Z v)) (hProduct (Z.symm z))
    exact hLeft.trans (hSub.trans (hCancel.trans (hProd.trans
      (nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 G z).symm)))
  apply ContinuousLinearMap.ext
  intro u
  refine (denseRange_sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).induction_on u ?_ ?_
  · exact isClosed_eq A.continuous B.continuous
  · intro z
    exact hPoint z

end OAI.AnisotropicCalderon.NativeNegativeHalfCoefficientCoordinateProduct
#print axioms OAI.AnisotropicCalderon.NativeNegativeHalfCoefficientCoordinateProduct.nativeNegativeHalfCoefficientMulL_zero_inclusion
#print axioms OAI.AnisotropicCalderon.NativeNegativeHalfCoefficientCoordinateProduct.nativeNegativeHalfCoefficientMulL_coordinate_comp_eq
