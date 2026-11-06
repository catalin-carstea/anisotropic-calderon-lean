import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility
import Calderon.SphereSobolevTangentialDerivative
import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.NativeNegativeHalfSmoothMultiplier
import Calderon.SphereSobolevCoordinateNegativeHalfOrder

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeNegativeHalfSmoothMultiplier

/-! Upfront: day-oct13/actual-boundary-moving-operator-oct15-v001/
EXPANSION-high-boundary-action.md. Literal compatible native endpoints. -/

theorem nativeCoefficientMulL_half_negative_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F) =
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  rw [nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg,
    nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg]
  apply ContinuousLinearMap.ext
  intro f
  exact (nativeNegativeHalfSmoothMulL_inclusion hF hO hD τ0
    (coefficientSmoothData F) hM hm hg f).symm

theorem sphereSobolevRotationL_threehalf_half_compatibility (i j : Fin 3) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevRotationL (3/2 : ℝ) i j) =
    (sphereSobolevRotationL (1/2 : ℝ) i j).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  have h := sphereSobolevRotationL_inclusion_comm (3/2 : ℝ) (1/2 : ℝ) (by norm_num) i j
  have hOrders :
      sphereSobolevInclusionL ((3/2 : ℝ)-1) ((1/2 : ℝ)-1) (by norm_num) =
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) := by
    have hDelta : ((1/2 : ℝ)-1)-((3/2 : ℝ)-1) =
        (-(1/2 : ℝ))-(1/2 : ℝ) := by norm_num
    apply ContinuousLinearMap.ext
    intro u
    apply lp.ext
    funext k
    have hLeft := sphereSobolevInclusionL_apply
      ((3/2 : ℝ)-1) ((1/2 : ℝ)-1) (by norm_num) u k
    have hRight := sphereSobolevInclusionL_apply
      (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u k
    exact hLeft.trans ((congrArg (fun r : ℝ => SpectralWeightedGraph.besselWeight r k • u k)
      hDelta).trans hRight.symm)
  rw [hOrders] at h
  exact h

def sphereThreeHalfTangentialDerivativeL
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ j : Fin 3, (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
    (EuclideanSpace.single j 1)).comp (sphereSobolevRotationL (3/2 : ℝ) j i)

theorem sphereTangentialDerivativeL_threehalf_half_compatibility
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereThreeHalfTangentialDerivativeL hF hO hD i) =
    (sphereTangentialDerivativeL hF hO hD i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hTerm (j : Fin 3) :
      Iout (sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
        (EuclideanSpace.single j 1) (sphereSobolevRotationL (3/2 : ℝ) j i f)) =
      sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
        (EuclideanSpace.single j 1) (sphereSobolevRotationL (1/2 : ℝ) j i (Iin f)) := by
    have hMul := sphereSobolevInclusionL_linearCoordinateMul
      hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (EuclideanSpace.single j 1) (sphereSobolevRotationL (3/2 : ℝ) j i f)
    have hRot := congrArg
      (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T f)
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
    exact hMul.trans (congrArg
      (sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
        (EuclideanSpace.single j 1)) hRot)
  simp only [ContinuousLinearMap.comp_apply,sphereThreeHalfTangentialDerivativeL,
    sphereTangentialDerivativeL,ContinuousLinearMap.sum_apply,map_sum,
    sphereSobolevLinearCoordinateMulL_negative_half_notation_eq]
  exact Finset.sum_congr rfl (fun j hj => hTerm j)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeCoefficientMulL_half_negative_compatibility
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_threehalf_half_compatibility
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereThreeHalfTangentialDerivativeL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereTangentialDerivativeL_threehalf_half_compatibility
