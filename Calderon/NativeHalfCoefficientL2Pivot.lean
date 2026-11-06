import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.NativeSmoothMultiplierCommonSupportJets
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open EnergyBridge DirichletFamily SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier DirichletFamily.DriftBootstrap
attribute [local irreducible] nativeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevZeroEquiv sphereContinuousScalarMulL

lemma sphereContinuousScalarMulL_inner_left_eq_right
    (m : C(UnitSphere,ℝ)) (u v : SphereL2) :
    ⟪sphereContinuousScalarMulL m u,v⟫_ℝ = ⟪u,sphereContinuousScalarMulL m v⟫_ℝ := by
  have hu : sphereContinuousScalarMulL m u =ᵐ[sphereProbability] (fun x => m x*u x) := by
    unfold sphereContinuousScalarMulL
    change sphereContinuousScalarMul m u =ᵐ[sphereProbability] _
    exact sphereContinuousScalarMul_value_ae m u
  have hv : sphereContinuousScalarMulL m v =ᵐ[sphereProbability] (fun x => m x*v x) := by
    unfold sphereContinuousScalarMulL
    change sphereContinuousScalarMul m v =ᵐ[sphereProbability] _
    exact sphereContinuousScalarMul_value_ae m v
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hv] with x hux hvx
  rw [Real.inner_apply,Real.inner_apply,hux,hvx]
  ring

lemma nativeHalfCoefficientMulL_lowerJets_inner_zero_left_eq_right
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (u v : SphereSobolev (1/2 : ℝ)) :
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) u),
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v⟫_ℝ =
    ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) u,
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) v)⟫_ℝ := by
  let I : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let M := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let m := smoothSphereValue (nativeH2CoefficientSmoothData Q)
  let C := sphereContinuousScalarMulL m
  let au := Z.symm (I u)
  let av := Z.symm (I v)
  have hValue (w : SphereSobolev (1/2 : ℝ)) : I (M w) = Z (C (Z.symm (I w))) :=
    sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0 Q
      (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm w
  have hLeft : ⟪I (M u),I v⟫_ℝ = ⟪C au,av⟫_ℝ :=
    (congrArg₂ (fun a b : SphereSobolev 0 => ⟪a,b⟫_ℝ) (hValue u) (Z.apply_symm_apply (I v)).symm).trans
      (Z.inner_map_map (C au) av)
  have hRight : ⟪I u,I (M v)⟫_ℝ = ⟪au,C av⟫_ℝ :=
    (congrArg₂ (fun a b : SphereSobolev 0 => ⟪a,b⟫_ℝ) (Z.apply_symm_apply (I u)).symm (hValue v)).trans
      (Z.inner_map_map au (C av))
  exact hLeft.trans ((sphereContinuousScalarMulL_inner_left_eq_right m au av).trans hRight.symm)

local instance nativeHalfPivotHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

lemma nativeNegativeHalfCoefficientMulL_dualPairing_left_eq_right
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 2) (z : SphereSobolev (-(1/2 : ℝ)))
    (y : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 Q z) y =
    sphereSobolevDualPairing (-(1/2 : ℝ)) z
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q y) := by
  unfold nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL realHilbertOperatorAdjointL
    sphereSobolevDualPairing
  change ⟪ContinuousLinearMap.adjoint (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q) z,y⟫_ℝ = _
  exact ContinuousLinearMap.adjoint_inner_left (nativeHalfCoefficientMulL hcalc hF hO hD τ0 Q) y z
end OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
