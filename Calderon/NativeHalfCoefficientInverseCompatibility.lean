import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeSmoothMultiplierInverse
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeHalfCoefficientInverseCompatibility
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeHalfSmoothMultiplier NativeSmoothMultiplierInverse

lemma inverse_comp_intertwiner_of_comp_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E) (B : F →L[ℝ] F) (I : E →L[ℝ] F)
    (hA : A.IsInvertible) (hB : B.IsInvertible) (hI : I.comp A = B.comp I) :
    I.comp A.inverse = B.inverse.comp I := by
  apply ContinuousLinearMap.ext
  intro x
  have hPoint : I (A (A.inverse x)) = B (I (A.inverse x)) :=
    congrArg (fun T : E →L[ℝ] F => T (A.inverse x)) hI
  have hValue : B (I (A.inverse x)) = I x :=
    hPoint.symm.trans (congrArg I (hA.self_apply_inverse x))
  exact (hB.inverse_apply_self (I (A.inverse x))).symm.trans (congrArg B.inverse hValue)

lemma nativeHalfCoefficientMulL_isInvertible_of_pos
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (hpos : ∀ x : UnitSphere, 0 < coefficientValue 2 F x.1) :
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible := by
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  have hEq := nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hgm
  obtain ⟨n,N,hN,hn,hgn,_,_,hHalf,hHalf',_,_⟩ :=
    exists_nativeSmoothMulL_two_sided_inverse hF hO hD τ0 (coefficientSmoothData F) hM hm hgm hpos
  have hInv : (nativeHalfSmoothMulL hF hO hD τ0 (coefficientSmoothData F) hM hm hgm).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hHalf hHalf'
  exact Eq.mp (congrArg
    (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T.IsInvertible) hEq.symm) hInv

end OAI.AnisotropicCalderon.NativeHalfCoefficientInverseCompatibility
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientInverseCompatibility.inverse_comp_intertwiner_of_comp_eq
#print axioms OAI.AnisotropicCalderon.NativeHalfCoefficientInverseCompatibility.nativeHalfCoefficientMulL_isInvertible_of_pos
