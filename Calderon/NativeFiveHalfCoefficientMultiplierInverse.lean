import Calderon.NativeFiveHalfCoefficientMultiplier
import Calderon.NativeThreeHalfCoefficientMultiplierInverse
import Calderon.NativeHalfCoefficientInverseCompatibility

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplierInverse
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeFiveHalfCoefficientMultiplier NativeThreeHalfCoefficientMultiplier
  NativeThreeHalfCoefficientMultiplierInverse NativeHalfCoefficientInverseCompatibility

lemma sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL_repacked
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 4) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F u) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (coefficientRepackedJets 4 3 F)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) :=
  sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
    F (coefficientRepackedJets 4 3 F) (coefficientValue_repackedJets 4 3 F).symm u

lemma nativeFiveHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G : SmoothCoefficientJets 4)
    (hmn : ∀ x : UnitSphere, coefficientValue 4 F x.1 * coefficientValue 4 G x.1 = 1) :
    (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 G) =
      ContinuousLinearMap.id ℝ (SphereSobolev (5/2:ℝ)) := by
  have hmn3 : ∀ x : UnitSphere,
      coefficientValue 3 (coefficientRepackedJets 4 3 F) x.1 *
        coefficientValue 3 (coefficientRepackedJets 4 3 G) x.1 = 1 := by
    intro x
    rw [coefficientValue_repackedJets,coefficientValue_repackedJets]
    exact hmn x
  have hLow := nativeThreeHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    hcalc hF hO hD τ0 (coefficientRepackedJets 4 3 F) (coefficientRepackedJets 4 3 G) hmn3
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (5/2:ℝ) (3/2:ℝ) (by norm_num)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
  rw [sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL_repacked,
    sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL_repacked]
  have hApply := DFunLike.congr_fun hLow
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hApply

lemma exists_nativeFiveHalfCoefficientMulL_reciprocal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 4)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 4 F x.1) :
    ∃ G : SmoothCoefficientJets 4,
      (∀ x : UnitSphere, coefficientValue 4 G x.1 = (coefficientValue 4 F x.1)⁻¹) ∧
      (∀ x : R3, (‖x‖ ≤ (1/2:ℝ) ∨ 2 ≤ ‖x‖) → coefficientValue 4 G x = 0) ∧
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
        (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 G) =
        ContinuousLinearMap.id ℝ (SphereSobolev (5/2:ℝ)) ∧
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 G).comp
        (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F) =
        ContinuousLinearMap.id ℝ (SphereSobolev (5/2:ℝ)) := by
  let f : SmoothData := ⟨coefficientValue 4 F,contDiff_coefficientValue 4 F⟩
  obtain ⟨n,hnCompact,hnSphere,hnAnnulus⟩ := exists_smoothData_sphere_reciprocal f hpos
  let G := compactCoefficient 4 n.1 n.2 hnCompact
  have hG : coefficientValue 4 G = n.1 := coefficientValue_compactCoefficient 4 n.1 n.2 hnCompact
  have hmn : ∀ x : UnitSphere, coefficientValue 4 F x.1 * coefficientValue 4 G x.1 = 1 := by
    intro x
    rw [hG,hnSphere x]
    exact mul_inv_cancel₀ (hpos x).ne'
  have hnm : ∀ x : UnitSphere, coefficientValue 4 G x.1 * coefficientValue 4 F x.1 = 1 := by
    intro x
    rw [mul_comm]
    exact hmn x
  refine ⟨G,?_,?_,nativeFiveHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
    hcalc hF hO hD τ0 F G hmn,nativeFiveHalfCoefficientMulL_comp_eq_id_of_sphere_mul_eq_one
      hcalc hF hO hD τ0 G F hnm⟩
  · intro x
    exact (congrFun hG x.1).trans (hnSphere x)
  · intro x hx
    exact (congrFun hG x).trans (hnAnnulus x hx)

lemma nativeFiveHalfCoefficientMulL_isInvertible_of_pos
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 4)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 4 F x.1) :
    (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F).IsInvertible := by
  obtain ⟨G,_,_,hFG,hGF⟩ := exists_nativeFiveHalfCoefficientMulL_reciprocal hcalc hF hO hD τ0 F hpos
  exact ContinuousLinearMap.IsInvertible.of_inverse hFG hGF

lemma sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 4) (G : SmoothCoefficientJets 3)
    (hFG : coefficientValue 4 F = coefficientValue 3 G)
    (hpos : ∀ x : UnitSphere, 0 < coefficientValue 4 F x.1) :
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F).inverse =
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G).inverse.comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  have hposG : ∀ x : UnitSphere, 0 < coefficientValue 3 G x.1 := by
    intro x
    rw [← hFG]
    exact hpos x
  apply inverse_comp_intertwiner_of_comp_eq
  · exact nativeFiveHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0 F hpos
  · exact nativeThreeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0 G hposG
  · apply ContinuousLinearMap.ext
    intro u
    exact sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F G hFG u

end OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplierInverse
