import Calderon.NativeH2ConormalRadialConversion
import Calderon.NativeCoefficientBoundaryMultiplier
import Calderon.ActualReferenceRadialEndpointCompatibility

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/suffix-repairs-v001/
EXPANSION-suffix-typed-parent-proofs-v001.md. Exact generic actual coefficient data graphs. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeFullSharpHalfTrace NativeNegativeHalfSmoothMultiplier

attribute [local irreducible] ordinaryConormalTraceL outwardRadialTraceL
  nativeHalfTraceL nativeNegativeHalfCoefficientMulL sphereTangentialDerivativeL
  sphereSobolevInclusionL sphereSobolevZeroEquiv coefficientSmoothData
  boundaryNormalCoefficientData boundaryTangentCoefficientData
  nativeNegativeHalfSmoothMulL TauCeti.Wkp.firstOrder

theorem nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (A : SmoothCoefficientJets 2)
    (T : Fin 3 → SmoothCoefficientJets 2)
    (hAData : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (hTData : ∀ j, coefficientSmoothData (T j) = boundaryTangentCoefficientData F j)
    (U : BallSobolev 2) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 F U)) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U))) +
    ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j)
      (sphereTangentialDerivativeL hF hO hD j
        (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) := by
  have hNormalBounds : ∃ M : ℝ, 0 ≤ M ∧
      (∀ x ∈ (ballOpens : Set R3), |(boundaryNormalCoefficientData F).1 x| ≤ M) ∧
      (∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryNormalCoefficientData F).1 x‖ ≤ M) :=
    exists_smooth_ball_multiplier_bound (boundaryNormalCoefficientData F)
  obtain ⟨M,hM,hm,hgrad⟩ := hNormalBounds
  have hTBounds (j : Fin 3) : ∃ N : ℝ, 0 ≤ N ∧
      (∀ x ∈ (ballOpens : Set R3), |(boundaryTangentCoefficientData F j).1 x| ≤ N) ∧
      (∀ x ∈ (ballOpens : Set R3), ‖gradient (boundaryTangentCoefficientData F j).1 x‖ ≤ N) :=
    exists_smooth_ball_multiplier_bound (boundaryTangentCoefficientData F j)
  choose N hN ht hgt using hTBounds
  let J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0 := sphereSobolevZeroEquiv hO hD
  let c : SphereSobolev (-(1/2 : ℝ)) := J (Z (ordinaryConormalTraceL hcalc τ0 F U))
  let r : SphereSobolev (-(1/2 : ℝ)) := J (Z (outwardRadialTraceL hcalc τ0 U))
  let b (j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
    sphereTangentialDerivativeL hF hO hD j
      (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))
  let M0 : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryNormalCoefficientData F) hM hm hgrad
  let Mt (j : Fin 3) : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    nativeNegativeHalfSmoothMulL hF hO hD τ0 (boundaryTangentCoefficientData F j)
      (hN j) (ht j) (hgt j)
  have hA : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A = M0 :=
    referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
      hcalc hF hO hD τ0 A (boundaryNormalCoefficientData F) hAData hM hm hgrad
  have hT (j : Fin 3) : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j) = Mt j :=
    referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
      hcalc hF hO hD τ0 (T j) (boundaryTangentCoefficientData F j) (hTData j)
        (hN j) (ht j) (hgt j)
  have hConversion : c = M0 r + ∑ j : Fin 3, Mt j (b j) :=
    nativeH2_conormal_negativeHalf_eq_normal_add_tangent
      hcalc hF hO hD τ0 F hM hm hgrad hN ht hgt U
  have hNormalValue : M0 r = nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 A r :=
    congrArg (fun K : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K r) hA.symm
  have hSum : (∑ j : Fin 3, Mt j (b j)) =
      ∑ j : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T j) (b j) :=
    Finset.sum_congr rfl (fun j hj =>
      congrArg (fun K : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => K (b j)) (hT j).symm)
  exact hConversion.trans
    (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x + y) hNormalValue hSum)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
