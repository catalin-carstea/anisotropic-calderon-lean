import Calderon.NativeNegativeHalfCoefficientCoordinateProduct
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-native-linear-scalar-identification-v055.md. Exact scalar graph
identifies existing native maps; actual gauge operator firstjet is separate. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeHalfSmoothMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct

lemma sphereLinearCoordinateMulL_eq_linear_scalarMulL (d : R3) :
    sphereLinearCoordinateMulL d =
      sphereContinuousScalarMulL (∑ i : Fin 3, (d i) • sphereCoordinate i) := by
  unfold sphereLinearCoordinateMulL
  simp_rw [sphereCoordinateMulL_eq_scalarMulL]
  change (∑ i : Fin 3, (d i) • sphereContinuousScalarMultiplierL (sphereCoordinate i)) =
    sphereContinuousScalarMultiplierL (∑ i : Fin 3, (d i) • sphereCoordinate i)
  rw [map_sum]
  simp only [map_smul]

attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevLinearCoordinateMulL

lemma nativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (d : R3)
    (hSphere : smoothSphereValue (coefficientSmoothData F) =
      ∑ i : Fin 3, (d i) • sphereCoordinate i) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d := by
  let I := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  have hScalar : sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) =
      sphereLinearCoordinateMulL d :=
    (congrArg (fun m => sphereContinuousScalarMulL m) hSphere).trans
      (sphereLinearCoordinateMulL_eq_linear_scalarMulL d).symm
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  have hNative := nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  have hNativeGraph : I (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F u) =
      Z (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) (Z.symm (I u))) :=
    (congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => I (A u)) hNative).trans
      (sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hg u)
  have hLinearGraph : I (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d u) =
      Z (sphereLinearCoordinateMulL d (Z.symm (I u))) :=
    sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (1/2 : ℝ) (by norm_num)
      d u (Z.symm (I u)) (Z.apply_symm_apply (I u)).symm
  exact hNativeGraph.trans
    ((congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm (I u)))) hScalar).trans hLinearGraph.symm)

lemma nativeNegativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (d : R3)
    (hSphere : smoothSphereValue (coefficientSmoothData F) =
      ∑ i : Fin 3, (d i) • sphereCoordinate i) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d := by
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let M0 := sphereSobolevLinearCoordinateMulL hF hO hD 0 d
  let Mn := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d
  let N := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F
  have hScalar : sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) =
      sphereLinearCoordinateMulL d :=
    (congrArg (fun m => sphereContinuousScalarMulL m) hSphere).trans
      (sphereLinearCoordinateMulL_eq_linear_scalarMulL d).symm
  have hPoint (z : SphereSobolev 0) : N (J z) = Mn (J z) := by
    have hNative := nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 F z
    have hLinear : M0 z = Z (sphereLinearCoordinateMulL d (Z.symm z)) :=
      (congrArg M0 (Z.apply_symm_apply z).symm).trans
        (sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD d (Z.symm z))
    have hScalarPoint := congrArg
      (fun A : SphereL2 →L[ℝ] SphereL2 => J (Z (A (Z.symm z)))) hScalar
    have hLinearPoint := congrArg J hLinear.symm
    have hCompat := sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0
      (-(1/2 : ℝ)) (by norm_num) d z
    exact hNative.trans (hScalarPoint.trans (hLinearPoint.trans hCompat))
  apply ContinuousLinearMap.ext
  intro u
  exact denseRange_clm_apply_eq J
    (denseRange_sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) N Mn hPoint u

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLinearCoordinateMulL_eq_linear_scalarMulL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeNegativeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue
