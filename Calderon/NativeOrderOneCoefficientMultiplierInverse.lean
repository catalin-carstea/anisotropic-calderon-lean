import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SmoothSphereReciprocal
import Calderon.SphereContinuousScalarMultiplierProduct

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse
open EnergyBridge DirichletFamily SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier

lemma nativeOrderOneCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 G3 : SmoothCoefficientJets 3) (F2 G2 : SmoothCoefficientJets 2)
    (hFval : coefficientValue 3 F3 = coefficientValue 2 F2)
    (hGval : coefficientValue 3 G3 = coefficientValue 2 G2)
    (hmn : ∀ x : UnitSphere, coefficientValue 3 F3 x.1 * coefficientValue 3 G3 x.1 = 1) :
    (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hFval).comp
      (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 G3 G2 hGval) =
      ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let MF := nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hFval
  let MG := nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 G3 G2 hGval
  let CF := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F3))
  let CG := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData G3))
  have hOuter : I (MF (MG f)) = Z (CF (Z.symm (I (MG f)))) :=
    sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero hcalc hF hO hD τ0 F3 F2 hFval (MG f)
  have hInner : I (MG f) = Z (CG (Z.symm (I f))) :=
    sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero hcalc hF hO hD τ0 G3 G2 hGval f
  have hSub := congrArg (fun z : SphereSobolev 0 => Z (CF (Z.symm z))) hInner
  have hCancel := congrArg (fun z : SphereL2 => Z (CF z)) (Z.symm_apply_apply (CG (Z.symm (I f))))
  have hL2 := sphereContinuousScalarMulL_comp_eq_id_of_mul_eq_one
    (smoothSphereValue (nativeH2CoefficientSmoothData F3))
    (smoothSphereValue (nativeH2CoefficientSmoothData G3)) hmn
  have hProduct := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm (I f)))) hL2
  exact hOuter.trans (hSub.trans (hCancel.trans (hProduct.trans (Z.apply_symm_apply (I f)))))

lemma exists_nativeOrderOneCoefficientMulL_reciprocal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hFval : coefficientValue 3 F3 = coefficientValue 2 F2)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 3 F3 x.1) :
    ∃ G3 : SmoothCoefficientJets 3, ∃ G2 : SmoothCoefficientJets 2,
      ∃ hGval : coefficientValue 3 G3 = coefficientValue 2 G2,
      (∀ x : UnitSphere, coefficientValue 3 G3 x.1 = (coefficientValue 3 F3 x.1)⁻¹) ∧
      (∀ x : R3, (‖x‖ ≤ (1/2:ℝ) ∨ 2 ≤ ‖x‖) → coefficientValue 3 G3 x = 0) ∧
      (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hFval).comp
        (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 G3 G2 hGval) =
        ContinuousLinearMap.id ℝ (SphereSobolev 1) ∧
      (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 G3 G2 hGval).comp
        (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hFval) =
        ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
  obtain ⟨n,hnCompact,hnSphere,hnAnnulus⟩ :=
    exists_smoothData_sphere_reciprocal (nativeH2CoefficientSmoothData F3) hpos
  let G3 := compactCoefficient 3 n.1 n.2 hnCompact
  let G2 := compactCoefficient 2 n.1 n.2 hnCompact
  have hG3 : coefficientValue 3 G3 = n.1 := coefficientValue_compactCoefficient 3 n.1 n.2 hnCompact
  have hG2 : coefficientValue 2 G2 = n.1 := coefficientValue_compactCoefficient 2 n.1 n.2 hnCompact
  have hGval : coefficientValue 3 G3 = coefficientValue 2 G2 := hG3.trans hG2.symm
  have hmn : ∀ x : UnitSphere, coefficientValue 3 F3 x.1 * coefficientValue 3 G3 x.1 = 1 := by
    intro x
    rw [hG3,hnSphere x]
    exact mul_inv_cancel₀ (hpos x).ne'
  have hnm : ∀ x : UnitSphere, coefficientValue 3 G3 x.1 * coefficientValue 3 F3 x.1 = 1 := by
    intro x
    rw [mul_comm]
    exact hmn x
  refine ⟨G3,G2,hGval,?_,?_,nativeOrderOneCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    hcalc hF hO hD τ0 F3 G3 F2 G2 hFval hGval hmn,
    nativeOrderOneCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
      hcalc hF hO hD τ0 G3 F3 G2 F2 hGval hFval hnm⟩
  · intro x
    exact (congrFun hG3 x.1).trans (hnSphere x)
  · intro x hx
    exact (congrFun hG3 x).trans (hnAnnulus x hx)

lemma nativeOrderOneCoefficientMulL_isInvertible_of_pos
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hFval : coefficientValue 3 F3 = coefficientValue 2 F2)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 3 F3 x.1) :
    (nativeOrderOneCoefficientMulL hcalc hF hO hD τ0 F3 F2 hFval).IsInvertible := by
  obtain ⟨G3,G2,hGval,_,_,hFG,hGF⟩ := exists_nativeOrderOneCoefficientMulL_reciprocal
    hcalc hF hO hD τ0 F3 F2 hFval hpos
  exact ContinuousLinearMap.IsInvertible.of_inverse hFG hGF

end OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse.nativeOrderOneCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse.exists_nativeOrderOneCoefficientMulL_reciprocal
#print axioms OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse.nativeOrderOneCoefficientMulL_isInvertible_of_pos
