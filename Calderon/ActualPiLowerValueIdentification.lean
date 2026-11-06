import Calderon.ActualPiNativeValueIdentification
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.NativeLinearCoordinateMultiplierIdentification

/-! Exact original Pi identities at Half and Neg. Half uses dense high inclusion, Neg dense zero inclusion. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct
attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL sphereSobolevInclusionL sphereSobolevLinearCoordinateMulL
  sphereSobolevZeroEquiv

lemma nativeHalfCoefficientMulL_eq_originalPi_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q3 : SmoothCoefficientJets 3) (Q2 : SmoothCoefficientJets 2)
    (N3 : Fin 3 → SmoothCoefficientJets 3) (N2 : Fin 3 → SmoothCoefficientJets 2)
    (hQ : coefficientValue 3 Q3 = coefficientValue 2 Q2)
    (hN : ∀ j, coefficientValue 3 (N3 j) = coefficientValue 2 (N2 j))
    (i : Fin 3) (a c : ℝ)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData Q3) =
      sphereCoordinate i + a • (∑ j : Fin 3,
        sphereCoordinate j * smoothSphereValue (nativeH2CoefficientSmoothData (N3 j))) +
      c • (1 : C(UnitSphere,ℝ))) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1) +
      a • (∑ j : Fin 3,
        (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)).comp
          (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (N2 j))) +
      c • ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let PH := sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single i 1) +
    a • (∑ j : Fin 3,
      (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (N3 j))) +
    c • ContinuousLinearMap.id ℝ (SphereSobolev (3/2 : ℝ))
  let PL := sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single i 1) +
    a • (∑ j : Fin 3,
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)).comp
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (N2 j))) +
    c • ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ))
  have hHigh : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q3 = PH :=
    nativeThreeHalfCoefficientMulL_eq_originalPi_of_sphereValue hcalc hF hO hD τ0 Q3 N3 i a c hSphere
  have hQGraph (v : SphereSobolev (3/2 : ℝ)) :
      I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q3 v) =
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (I v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q3 Q2 hQ)
  have hNGraph (j : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (N3 j) v) =
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (N2 j) (I v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 (N3 j) (N2 j) (hN j))
  have hCoordinate (j : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      I (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1) v) =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1) (I v) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (EuclideanSpace.single j 1) v
  have hPoint (v : SphereSobolev (3/2 : ℝ)) :
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2 (I v) = PL (I v) := by
    calc
      _ = I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q3 v) := (hQGraph v).symm
      _ = I (PH v) := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) => I (A v)) hHigh
      _ = _ := by
        simp only [PH,PL,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
          map_add,map_smul,map_sum,hCoordinate,hNGraph]
  apply ContinuousLinearMap.ext
  intro u
  exact denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q2) PL hPoint u

lemma nativeNegativeHalfCoefficientMulL_eq_originalPi_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 2) (N : Fin 3 → SmoothCoefficientJets 2)
    (i : Fin 3) (a c : ℝ)
    (hSphere : smoothSphereValue (coefficientSmoothData Q) =
      sphereCoordinate i + a • (∑ j : Fin 3,
        sphereCoordinate j * smoothSphereValue (coefficientSmoothData (N j))) +
      c • (1 : C(UnitSphere,ℝ))) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q =
      sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single i 1) +
      a • (∑ j : Fin 3,
        (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)).comp
          (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (N j))) +
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) := by
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let P := sphereContinuousScalarMultiplierL
  let V (F : SmoothCoefficientJets 2) := smoothSphereValue (coefficientSmoothData F)
  let M (j : Fin 3) := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
  let NN (j : Fin 3) := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (N j)
  let PL := M i + a • (∑ j : Fin 3, (M j).comp (NN j)) +
    c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ)))
  have hProduct (j : Fin 3) : P (sphereCoordinate j * V (N j)) =
      (P (sphereCoordinate j)).comp (P (V (N j))) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (sphereContinuousScalarMulL_mul_apply (sphereCoordinate j) (V (N j)) v).symm
  have hOne : P (1 : C(UnitSphere,ℝ)) = ContinuousLinearMap.id ℝ SphereL2 := sphereContinuousScalarMulL_one
  have hScalar : P (V Q) = P (sphereCoordinate i) +
      a • (∑ j : Fin 3, (P (sphereCoordinate j)).comp (P (V (N j)))) +
      c • ContinuousLinearMap.id ℝ SphereL2 := by
    have hv : V Q = sphereCoordinate i +
        a • (∑ j : Fin 3, sphereCoordinate j * V (N j)) + c • (1 : C(UnitSphere,ℝ)) := hSphere
    rw [hv]
    simp only [map_add,map_smul,map_sum,hProduct,hOne]
  have hValue (F : SmoothCoefficientJets 2) (v : SphereSobolev 0) :
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F (J v) =
        J (Z (P (V F) (Z.symm v))) :=
    nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 F v
  have hCoordinate (j : Fin 3) (v : SphereSobolev 0) :
      M j (J v) = J (Z (P (sphereCoordinate j) (Z.symm v))) := by
    let M0 := sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1)
    have hZero : M0 v = Z (sphereLinearCoordinateMulL (EuclideanSpace.single j 1) (Z.symm v)) :=
      (congrArg M0 (Z.apply_symm_apply v).symm).trans
        (sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD (EuclideanSpace.single j 1) (Z.symm v))
    have hCompat := sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-(1/2 : ℝ))
      (by norm_num) (EuclideanSpace.single j 1) v
    have hh := hCompat.symm.trans (congrArg J hZero)
    change sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) v) =
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (Z (sphereContinuousScalarMulL (sphereCoordinate j) (Z.symm v)))
    simpa only [sphereLinearCoordinateMulL_single,sphereCoordinateMulL_eq_scalarMulL] using hh
  have hPoint (v : SphereSobolev 0) :
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q (J v) = PL (J v) := by
    have hComp (j : Fin 3) : M j (NN j (J v)) =
        J (Z (P (sphereCoordinate j) (P (V (N j)) (Z.symm v)))) := by
      rw [hValue,hCoordinate]
      simp only [Z.symm_apply_apply]
    dsimp only [J,M,NN] at hComp hCoordinate
    calc
      _ = J (Z (P (V Q) (Z.symm v))) := hValue Q v
      _ = J (Z ((P (sphereCoordinate i) +
          a • (∑ j : Fin 3, (P (sphereCoordinate j)).comp (P (V (N j)))) +
          c • ContinuousLinearMap.id ℝ SphereL2) (Z.symm v))) :=
        congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => J (Z (A (Z.symm v)))) hScalar
      _ = _ := by
        simp only [PL,M,NN,J,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
          map_add,map_smul,map_sum,hComp,hCoordinate,Z.apply_symm_apply]
  apply ContinuousLinearMap.ext
  intro u
  exact denseRange_clm_apply_eq J
    (denseRange_sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q) PL hPoint u

end OAI.AnisotropicCalderon.SphereHarmonic
