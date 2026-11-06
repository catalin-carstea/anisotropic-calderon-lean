import Calderon.ActualPiNativeGeometryCore
import Calderon.NativeThreeHalfCoefficientCoordinateProduct
import Calderon.NativeCoefficientMultiplierBoundaryDerivative

/-! Original X5 Pi high value formula (P4).
The coefficient-value hypothesis is a transparent matching contract, not an
existence/bound assumption for the physical family. That family is separate. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] nativeThreeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevLinearCoordinateMulL sphereSobolevZeroEquiv

lemma nativeThreeHalfCoefficientMulL_eq_originalPi_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (N : Fin 3 → SmoothCoefficientJets 3)
    (i : Fin 3) (a c : ℝ)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData Q) =
      sphereCoordinate i + a • (∑ j : Fin 3,
        sphereCoordinate j * smoothSphereValue (nativeH2CoefficientSmoothData (N j))) +
      c • (1 : C(UnitSphere,ℝ))) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q =
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1) +
      a • (∑ j : Fin 3,
        (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (N j))) +
      c • ContinuousLinearMap.id ℝ (SphereSobolev (3/2 : ℝ)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let P := sphereContinuousScalarMultiplierL
  let V (F : SmoothCoefficientJets 3) := smoothSphereValue (nativeH2CoefficientSmoothData F)
  let M (j : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
  let NN (j : Fin 3) := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (N j)
  have hProduct (j : Fin 3) : P (sphereCoordinate j * V (N j)) =
      (P (sphereCoordinate j)).comp (P (V (N j))) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (sphereContinuousScalarMulL_mul_apply (sphereCoordinate j) (V (N j)) v).symm
  have hOne : P (1 : C(UnitSphere,ℝ)) = ContinuousLinearMap.id ℝ SphereL2 :=
    sphereContinuousScalarMulL_one
  have hScalar : P (V Q) = P (sphereCoordinate i) +
      a • (∑ j : Fin 3, (P (sphereCoordinate j)).comp (P (V (N j)))) +
      c • ContinuousLinearMap.id ℝ SphereL2 := by
    have hv : V Q = sphereCoordinate i +
        a • (∑ j : Fin 3, sphereCoordinate j * V (N j)) + c • (1 : C(UnitSphere,ℝ)) := hSphere
    rw [hv]
    simp only [map_add,map_smul,map_sum,hProduct,hOne]
  have hValue (F : SmoothCoefficientJets 3) (v : SphereSobolev (3/2 : ℝ)) :
      I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F v) =
        Z (P (V F) (Z.symm (I v))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F v
  have hCoordinate (j : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      I (M j v) = Z (P (sphereCoordinate j) (Z.symm (I v))) := by
    have h := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD
      (3/2 : ℝ) (by norm_num) (EuclideanSpace.single j 1) v
      (Z.symm (I v)) (Z.apply_symm_apply (I v)).symm
    change sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) v) =
      sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (sphereCoordinate j) (Z.symm (I v)))
    simpa only [sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL] using h
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  have hComp (j : Fin 3) : I (M j (NN j u)) =
      Z (P (sphereCoordinate j) (P (V (N j)) (Z.symm (I u)))) := by
    rw [hCoordinate,hValue]
    simp only [Z.symm_apply_apply]
  dsimp only [I,M,NN] at hComp hCoordinate
  calc
    _ = Z (P (V Q) (Z.symm (I u))) := hValue Q u
    _ = Z ((P (sphereCoordinate i) +
        a • (∑ j : Fin 3, (P (sphereCoordinate j)).comp (P (V (N j)))) +
        c • ContinuousLinearMap.id ℝ SphereL2) (Z.symm (I u))) :=
      congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm (I u)))) hScalar
    _ = _ := by
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
        map_add,map_smul,map_sum,I,hComp,hCoordinate,Z.apply_symm_apply]

end OAI.AnisotropicCalderon.SphereHarmonic
