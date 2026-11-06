import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.SmoothSphereReciprocal
import Calderon.SphereContinuousScalarMultiplierProduct

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplierInverse
open EnergyBridge DirichletFamily SphereHarmonic NativeThreeHalfCoefficientMultiplier

lemma nativeThreeHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 3)
    (hmn : ∀ x : UnitSphere, coefficientValue 3 F x.1 * coefficientValue 3 G x.1 = 1) :
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  let MF := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F
  let MG := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G
  let CF := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
  let CG := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData G))
  have hOuter : I (MF (MG f)) = Z (CF (Z.symm (I (MG f)))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F (MG f)
  have hInner : I (MG f) = Z (CG (Z.symm (I f))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 G f
  have hSub := congrArg (fun z : SphereSobolev 0 => Z (CF (Z.symm z))) hInner
  have hCancel := congrArg (fun z : SphereL2 => Z (CF z)) (Z.symm_apply_apply (CG (Z.symm (I f))))
  have hL2 := sphereContinuousScalarMulL_comp_eq_id_of_mul_eq_one
    (smoothSphereValue (nativeH2CoefficientSmoothData F))
    (smoothSphereValue (nativeH2CoefficientSmoothData G)) hmn
  have hProduct := congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm (I f)))) hL2
  exact hOuter.trans (hSub.trans (hCancel.trans (hProduct.trans (Z.apply_symm_apply (I f)))))

lemma exists_nativeThreeHalfCoefficientMulL_reciprocal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 3 F x.1) :
    ∃ G : SmoothCoefficientJets 3,
      (∀ x : UnitSphere, coefficientValue 3 G x.1 = (coefficientValue 3 F x.1)⁻¹) ∧
      (∀ x : R3, (‖x‖ ≤ (1/2:ℝ) ∨ 2 ≤ ‖x‖) → coefficientValue 3 G x = 0) ∧
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
        ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)) ∧
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F) =
        ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)) := by
  obtain ⟨n,hnCompact,hnSphere,hnAnnulus⟩ :=
    exists_smoothData_sphere_reciprocal (nativeH2CoefficientSmoothData F) hpos
  let G := compactCoefficient 3 n.1 n.2 hnCompact
  have hG : coefficientValue 3 G = n.1 := coefficientValue_compactCoefficient 3 n.1 n.2 hnCompact
  have hmn : ∀ x : UnitSphere, coefficientValue 3 F x.1 * coefficientValue 3 G x.1 = 1 := by
    intro x
    rw [hG,hnSphere x]
    exact mul_inv_cancel₀ (hpos x).ne'
  have hnm : ∀ x : UnitSphere, coefficientValue 3 G x.1 * coefficientValue 3 F x.1 = 1 := by
    intro x
    rw [mul_comm]
    exact hmn x
  refine ⟨G,?_,?_,nativeThreeHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    hcalc hF hO hD τ0 F G hmn,nativeThreeHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
      hcalc hF hO hD τ0 G F hnm⟩
  · intro x
    exact (congrFun hG x.1).trans (hnSphere x)
  · intro x hx
    exact (congrFun hG x).trans (hnAnnulus x hx)

lemma nativeThreeHalfCoefficientMulL_isInvertible_of_pos
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 3 F x.1) :
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible := by
  obtain ⟨G,_,_,hFG,hGF⟩ := exists_nativeThreeHalfCoefficientMulL_reciprocal hcalc hF hO hD τ0 F hpos
  exact ContinuousLinearMap.IsInvertible.of_inverse hFG hGF

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplierInverse

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplierInverse.nativeThreeHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplierInverse.exists_nativeThreeHalfCoefficientMulL_reciprocal
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplierInverse.nativeThreeHalfCoefficientMulL_isInvertible_of_pos
