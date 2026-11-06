import Calderon.NativeLinearCoordinateMultiplierIdentification
import Calderon.OperatorCurveFixedArgumentDerivative

/-! Boundary scalar jets identify derivatives of the native multiplier maps. No chosen-jet smoothness premise. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeHalfSmoothMultiplier
  NativeNegativeHalfCoefficientCoordinateProduct OperatorCurveDerivative

lemma sphereContinuousScalarMulL_one :
    sphereContinuousScalarMulL (1 : C(UnitSphere,ℝ)) = ContinuousLinearMap.id ℝ SphereL2 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae (1 : C(UnitSphere,ℝ)) u] with x hx
  change sphereContinuousScalarMul (1 : C(UnitSphere,ℝ)) u x = u x
  exact hx.trans (one_mul (u x))

attribute [local irreducible] nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevLinearCoordinateMulL

lemma sphereSobolevInclusionL_nativeHalfCoefficientMulL_value
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 2) (u : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q u) =
    sphereSobolevZeroEquiv hO hD
      (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData Q))
        ((sphereSobolevZeroEquiv hO hD).symm
          (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) u))) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData Q)
  have hNative := nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 Q hM hm hg
  exact (congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (A u)) hNative).trans
      (sphereSobolevInclusionL_nativeHalfSmoothMulL hF hO hD τ0
        (coefficientSmoothData Q) hM hm hg u)

lemma nativeHalfCoefficientMulL_eq_id_of_sphereValue_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 2)
    (hOne : smoothSphereValue (coefficientSmoothData Q) = 1) :
    nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q =
      ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  have h := sphereSobolevInclusionL_nativeHalfCoefficientMulL_value hcalc hF hO hD τ0 Q u
  rw [hOne,sphereContinuousScalarMulL_one] at h
  simpa only [ContinuousLinearMap.id_apply,LinearIsometryEquiv.apply_symm_apply] using h

lemma nativeNegativeHalfCoefficientMulL_eq_id_of_sphereValue_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 2)
    (hOne : smoothSphereValue (coefficientSmoothData Q) = 1) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q =
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) := by
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let A := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  have hPoint (z : SphereSobolev 0) : A (J z) = J z := by
    have h := nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 Q z
    rw [hOne,sphereContinuousScalarMulL_one] at h
    simpa only [ContinuousLinearMap.id_apply,LinearIsometryEquiv.apply_symm_apply] using h
  apply ContinuousLinearMap.ext
  intro u
  exact denseRange_clm_apply_eq J
    (denseRange_sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) A
      (ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ)))) hPoint u

lemma hasDerivAt_nativeHalfCoefficientMulL_of_boundary_jet
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : ℝ → SmoothCoefficientJets 2) (d : R3)
    (hA : DifferentiableAt ℝ (fun r => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)) 0)
    (hm : HasDerivAt (fun r => smoothSphereValue (coefficientSmoothData (Q r)))
      (∑ i : Fin 3, (d i) • sphereCoordinate i) 0) :
    HasDerivAt (fun r => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r))
      (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d) 0 := by
  let A := fun r => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)
  let I := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let ell : C(UnitSphere,ℝ) := ∑ i : Fin 3, (d i) • sphereCoordinate i
  have hScalar := sphereContinuousScalarMultiplierL.hasFDerivAt.comp_hasDerivAt 0 hm
  have hDerivative : deriv A 0 = sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) d := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
    have hLeft := I.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_clm_fixed_argument_of_differentiableAt A 0 hA u)
    have hValue : HasDerivAt (fun r => sphereContinuousScalarMulL
        (smoothSphereValue (coefficientSmoothData (Q r))) (Z.symm (I u)))
        (sphereContinuousScalarMulL ell (Z.symm (I u))) 0 := by
      simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
        ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,
        sphereContinuousScalarMultiplierL_apply,map_zero,add_zero] using
        hScalar.clm_apply (hasDerivAt_const (0 : ℝ) (Z.symm (I u)))
    have hRight := Z.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hValue
    have hCurve : (fun r => I (A r u)) =ᶠ[𝓝 (0 : ℝ)] (fun r => Z
        (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (Q r)))
          (Z.symm (I u)))) := by
      apply Filter.Eventually.of_forall
      intro r
      exact sphereSobolevInclusionL_nativeHalfCoefficientMulL_value hcalc hF hO hD τ0 (Q r) u
    have hNative := hLeft.unique (hRight.congr_of_eventuallyEq hCurve)
    have hLinear := sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv
      hF hO hD (1/2 : ℝ) (by norm_num) d u (Z.symm (I u))
        (Z.apply_symm_apply (I u)).symm
    have hScalarId : sphereContinuousScalarMulL ell = sphereLinearCoordinateMulL d :=
      (sphereLinearCoordinateMulL_eq_linear_scalarMulL d).symm
    exact hNative.trans ((congrArg (fun T : SphereL2 →L[ℝ] SphereL2 =>
      Z (T (Z.symm (I u)))) hScalarId).trans hLinear.symm)
  have hFrechet := hA.hasFDerivAt
  have hd : HasDerivAt A (deriv A 0) 0 := hFrechet.hasDerivAt
  rw [hDerivative] at hd
  exact hd

lemma hasDerivAt_nativeNegativeHalfCoefficientMulL_of_boundary_jet
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : ℝ → SmoothCoefficientJets 2) (d : R3)
    (hA : DifferentiableAt ℝ (fun r => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)) 0)
    (hm : HasDerivAt (fun r => smoothSphereValue (coefficientSmoothData (Q r)))
      (∑ i : Fin 3, (d i) • sphereCoordinate i) 0) :
    HasDerivAt (fun r => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r))
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d) 0 := by
  let A := fun r => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (Q r)
  let J := sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let ell : C(UnitSphere,ℝ) := ∑ i : Fin 3, (d i) • sphereCoordinate i
  let Mn := sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) d
  let M0 := sphereSobolevLinearCoordinateMulL hF hO hD 0 d
  have hScalar := sphereContinuousScalarMultiplierL.hasFDerivAt.comp_hasDerivAt 0 hm
  have hPoint (z : SphereSobolev 0) : deriv A 0 (J z) = Mn (J z) := by
    have hLeft := hasDerivAt_clm_fixed_argument_of_differentiableAt A 0 hA (J z)
    have hValue : HasDerivAt (fun r => sphereContinuousScalarMulL
        (smoothSphereValue (coefficientSmoothData (Q r))) (Z.symm z))
        (sphereContinuousScalarMulL ell (Z.symm z)) 0 := by
      simpa only [HasDerivAt,HasDerivAtFilter,hasFDerivAtFilter_iff_isLittleOTVS,
        ContinuousLinearMap.toSpanSingleton_apply,Function.comp_def,
        sphereContinuousScalarMultiplierL_apply,map_zero,add_zero] using
        hScalar.clm_apply (hasDerivAt_const (0 : ℝ) (Z.symm z))
    have hZero := Z.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hValue
    have hRight := J.hasFDerivAt.comp_hasDerivAt 0 hZero
    have hCurve : (fun r => A r (J z)) =ᶠ[𝓝 (0 : ℝ)] (fun r => J (Z
        (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (Q r)))
          (Z.symm z)))) := by
      apply Filter.Eventually.of_forall
      intro r
      exact nativeNegativeHalfCoefficientMulL_zero_inclusion hcalc hF hO hD τ0 (Q r) z
    have hNative := hLeft.unique (hRight.congr_of_eventuallyEq hCurve)
    have hLinear : M0 z = Z (sphereLinearCoordinateMulL d (Z.symm z)) :=
      (congrArg M0 (Z.apply_symm_apply z).symm).trans
        (sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD d (Z.symm z))
    have hScalarId : sphereContinuousScalarMulL ell = sphereLinearCoordinateMulL d :=
      (sphereLinearCoordinateMulL_eq_linear_scalarMulL d).symm
    have hCompat := sphereSobolevInclusionL_linearCoordinateMul hF hO hD
      0 (-(1/2 : ℝ)) (by norm_num) d z
    exact hNative.trans ((congrArg (fun T : SphereL2 →L[ℝ] SphereL2 =>
      J (Z (T (Z.symm z)))) hScalarId).trans ((congrArg J hLinear.symm).trans hCompat))
  have hDerivative : deriv A 0 = Mn := by
    apply ContinuousLinearMap.ext
    intro u
    exact denseRange_clm_apply_eq J
      (denseRange_sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)) (deriv A 0) Mn hPoint u
  have hFrechet := hA.hasFDerivAt
  have hd : HasDerivAt A (deriv A 0) 0 := hFrechet.hasDerivAt
  rw [hDerivative] at hd
  exact hd

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereContinuousScalarMulL_one
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_nativeHalfCoefficientMulL_value
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeHalfCoefficientMulL_eq_id_of_sphereValue_one
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeNegativeHalfCoefficientMulL_eq_id_of_sphereValue_one
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_nativeHalfCoefficientMulL_of_boundary_jet
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.hasDerivAt_nativeNegativeHalfCoefficientMulL_of_boundary_jet
