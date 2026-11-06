import Calderon.SphereSobolevOrderOneRotation
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.ActualHarmonicPolynomialGreen

set_option autoImplicit false
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ContDiff ENNReal InnerProductSpace Gradient Classical
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotation SmoothSphereRotationProjection SmoothAngularCasimir
  NativeFullSharpHalfTrace SpectralCoreRegularity HarmonicPolynomialGreen
  NativeHarmonicBulkDerivativeMoments DirichletFamily EnergyBridge MetricVolume

def sphereTangentialDerivativeL (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
  ∑ j : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ)
    (EuclideanSpace.single j 1)).comp (sphereSobolevRotationL (1/2 : ℝ) j i)

lemma norm_sphereTangentialDerivativeL_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) :
    ‖sphereTangentialDerivativeL hF hO hD i‖ ≤
      ∑ j : Fin 3, ‖sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ)
        (EuclideanSpace.single j 1)‖ * Real.sqrt 2 := by
  unfold sphereTangentialDerivativeL
  refine (norm_sum_le Finset.univ (fun j : Fin 3 =>
    (sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ)
      (EuclideanSpace.single j 1)).comp (sphereSobolevRotationL (1/2 : ℝ) j i))).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_sphereSobolevRotationL_le (1/2 : ℝ) j i) (norm_nonneg (sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ) (EuclideanSpace.single j 1))))

/-- A globally smooth extension of the literal tangential field on the unit sphere. -/
def smoothTangentialData (f : SmoothData) (i : Fin 3) : SmoothData :=
  ⟨fun x : R3 => ∑ j : Fin 3, x j * sphereRotationDerivative j i f.1 x,
    ContDiff.sum fun j hj => (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.mul
      (contDiff_sphereRotationDerivative j i f.1 f.2)⟩

lemma smoothTangentialData_apply (f : SmoothData) (i : Fin 3) (x : UnitSphere) :
    (smoothTangentialData f i).1 x.val =
      fderiv ℝ f.1 x.val (coordinateVector i-x.val i • x.val) := by
  have hsum : (∑ j : Fin 3, x.val j • coordinateVector j) = x.val := by
    ext l
    simp [coordinateVector,Pi.single_apply]
  have hrad : fderiv ℝ f.1 x.val x.val =
      ∑ j : Fin 3, x.val j * fderiv ℝ f.1 x.val (coordinateVector j) := by
    calc
      _ = fderiv ℝ f.1 x.val (∑ j : Fin 3, x.val j • coordinateVector j) :=
        congrArg (fderiv ℝ f.1 x.val) hsum.symm
      _ = _ := by rw [map_sum]; simp only [map_smul,smul_eq_mul]
  change (∑ j : Fin 3, x.val j * fderiv ℝ f.1 x.val (rotationVector j i x.val)) = _
  simp only [rotationVector,map_sub,map_smul,smul_eq_mul]
  have he (j : Fin 3) : x.val j *
      (x.val j * fderiv ℝ f.1 x.val (coordinateVector i) -
        x.val i * fderiv ℝ f.1 x.val (coordinateVector j)) =
      (x.val j)^2 * fderiv ℝ f.1 x.val (coordinateVector i) -
        x.val i * (x.val j * fderiv ℝ f.1 x.val (coordinateVector j)) := by ring
  change (∑ j : Fin 3, x.val j *
    (x.val j * fderiv ℝ f.1 x.val (coordinateVector i) -
      x.val i * fderiv ℝ f.1 x.val (coordinateVector j))) = _
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,
    unitSphere_sum_sq,one_mul,← hrad]

lemma sum_coordinateMul_smoothRotation_eq_tangential
    (f : SmoothData) (i : Fin 3) :
    (∑ j : Fin 3, sphereCoordinateMulL j
      (smoothSphereLift (sphereRotationDerivative j i f.1)
        (contDiff_sphereRotationDerivative j i f.1 f.2))) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothTangentialData f i)) := by
  simp_rw [smoothSphereLift,sphereCoordinateMulL_toLp]
  rw [← map_sum]
  congr 1

lemma sphereTangentialDerivativeL_nativeHalfTrace_smooth
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) (i : Fin 3) :
    sphereTangentialDerivativeL hF hO hD i (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f)) =
      sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
        (sphereSobolevZeroEquiv hO hD
          ((ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothTangentialData f i)))) := by
  let b : SphereSobolev (1/2 : ℝ) := nativeHalfTraceL hF hO hD τ0 (smoothSobolev f)
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M (j : Fin 3) : SphereSobolev (-1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevLinearCoordinateMulL hF hO hD (-1/2 : ℝ) (EuclideanSpace.single j 1)
  let Q (j : Fin 3) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
    sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single j 1)
  let R (j : Fin 3) : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-1/2 : ℝ) :=
    sphereSobolevRotationL (1/2 : ℝ) j i
  let v (j : Fin 3) : SphereL2 := smoothSphereLift (sphereRotationDerivative j i f.1)
    (contDiff_sphereRotationDerivative j i f.1 f.2)
  have hterm (j : Fin 3) : M j (R j b) = J (Z (sphereCoordinateMulL j (v j))) := by
    have hrot : R j b = J (Z (v j)) :=
      sphereSobolevRotationL_nativeHalfTrace_smooth hF hO hD τ0 f j i
    have hinc : J (Q j (Z (v j))) = M j (J (Z (v j))) :=
      sphereSobolevInclusionL_linearCoordinateMul hF hO hD 0 (-1/2 : ℝ)
        (by norm_num) (EuclideanSpace.single j 1) (Z (v j))
    have hzero : Q j (Z (v j)) = Z (sphereCoordinateMulL j (v j)) :=
      (sphereSobolevLinearCoordinateMulL_zeroEquiv hF hO hD
        (EuclideanSpace.single j 1) (v j)).trans
          (congrArg (fun L : SphereL2 →L[ℝ] SphereL2 => Z (L (v j)))
            (sphereLinearCoordinateMulL_single j))
    exact (congrArg (M j) hrot).trans (hinc.symm.trans (congrArg J hzero))
  have hsum : sphereTangentialDerivativeL hF hO hD i b =
      ∑ j : Fin 3, M j (R j b) := by
    change (∑ j : Fin 3, (M j).comp (R j)) b = _
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  have hmap : (∑ j : Fin 3, J (Z (sphereCoordinateMulL j (v j)))) =
      J (Z (∑ j : Fin 3, sphereCoordinateMulL j (v j))) := by
    rw [map_sum,map_sum]
  have hvalue : J (Z (∑ j : Fin 3, sphereCoordinateMulL j (v j))) =
      J (Z ((ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothSphereValue (smoothTangentialData f i)))) :=
    congrArg (fun w : SphereL2 => J (Z w))
      (sum_coordinateMul_smoothRotation_eq_tangential f i)
  exact hsum.trans ((Finset.sum_congr rfl (fun j hj => hterm j)).trans (hmap.trans hvalue))

lemma sphereSobolevCoefficientL_tangential_nativeHalfTrace_smooth
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (f : SmoothData) (i : Fin 3) (k : ℕ) :
    sphereSobolevCoefficientL (-1/2 : ℝ) k
      (sphereTangentialDerivativeL hF hO hD i (nativeHalfTraceL hF hO hD τ0 (smoothSobolev f))) =
      sphereHarmonicCoordinate hO hD k
        ((ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothTangentialData f i))) := by
  rw [sphereTangentialDerivativeL_nativeHalfTrace_smooth,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv]

lemma smoothTangentialData_homogeneous_polynomial_apply
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k)
    (i : Fin 3) (x : UnitSphere) :
    (smoothTangentialData (smoothPolynomialData p) i).1 x.val =
      (pderiv i p).eval (polynomialCoordinateMap x.val) -
        x.val i * (k:ℝ) * p.eval (polynomialCoordinateMap x.val) := by
  rw [smoothTangentialData_apply,map_sub,map_smul,smul_eq_mul]
  have h := inner_polynomial_energyGradient_radial k p hp x.val
  rw [energyGradient_eq_gradient,inner_gradient_right] at h
  simp only [RCLike.conj_to_real] at h
  change fderiv ℝ (fun y : R3 => p.eval (polynomialCoordinateMap y)) x.val x.val =
    (k:ℝ)*p.eval (polynomialCoordinateMap x.val) at h
  change fderiv ℝ (fun y : R3 => p.eval (polynomialCoordinateMap y)) x.val (coordinateVector i) -
    x.val i*fderiv ℝ (fun y : R3 => p.eval (polynomialCoordinateMap y)) x.val x.val = _
  rw [h,fderiv_polynomialEval_coordinate]
  simp only [polynomialCoordinateMap_apply]
  ring

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTangentialDerivativeL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereTangentialDerivativeL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.smoothTangentialData
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.smoothTangentialData_apply
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sum_coordinateMul_smoothRotation_eq_tangential
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTangentialDerivativeL_nativeHalfTrace_smooth
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_tangential_nativeHalfTrace_smooth
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.smoothTangentialData_homogeneous_polynomial_apply
