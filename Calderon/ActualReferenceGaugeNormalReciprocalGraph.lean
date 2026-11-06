import Calderon.ActualReferenceGaugeNormalMultiplierInverse
import Calderon.NativeSmoothMultiplierInverse

/-! Full upfront: actual-gauge-tangent-operator-author-oct15-v001/reciprocal-graph-author-v001/
EXPANSION-inverse-graph-v001.md. Scalar boundary identity precedes native inverse identity. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeSmoothMultiplierInverse

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (y0 : R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceGaugeNormalHalfMultiplierFamily
  referenceGaugeNormalNegativeHalfMultiplierFamily ContinuousLinearMap.inverse
  referenceGaugeNormalCoefficientJetsFamily nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL

lemma referenceGaugeNormalHalfMultiplier_inverse_eq_native_reciprocal
    (p : ℝ × (R3 × ℝ)) (G : SmoothCoefficientJets 2)
    (hG : ∀ x : UnitSphere, coefficientValue 2 G x.val =
      (referenceGaugeNormalCoefficient g L Φ a (p,x.val))⁻¹) :
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  let F := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨N,hN,hn,hgn⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData G)
  have hFG : ∀ x : UnitSphere,
      (coefficientSmoothData F).1 x.val * (coefficientSmoothData G).1 x.val = 1 := by
    intro x
    change coefficientValue 2 F x.val * coefficientValue 2 G x.val = 1
    rw [coefficientValue_referenceGaugeNormalCoefficientJetsFamily,hG x]
    exact mul_inv_cancel₀ (ne_of_gt
      (referenceGaugeNormalCoefficient_sphere_pos g L Φ a y0 B ε C ρ H w hData p x))
  have hProd : (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
      ContinuousLinearMap.id ℝ (SphereSobolev (1/2 : ℝ)) := by
    unfold referenceGaugeNormalHalfMultiplierFamily
    change (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp _ = _
    rw [nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hgm,
      nativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 G hN hn hgn]
    exact nativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one hF hO hD τ0
      (coefficientSmoothData F) (coefficientSmoothData G) hM hN hm hgm hn hgn hFG
  have hi := (referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).1
  apply ContinuousLinearMap.ext
  intro u
  have hp := congrArg (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T u) hProd
  change referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) = u at hp
  exact (congrArg (referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse hp).symm.trans
    (hi.inverse_apply_self _)

lemma referenceGaugeNormalNegativeMultiplier_inverse_eq_native_reciprocal
    (p : ℝ × (R3 × ℝ)) (G : SmoothCoefficientJets 2)
    (hG : ∀ x : UnitSphere, coefficientValue 2 G x.val =
      (referenceGaugeNormalCoefficient g L Φ a (p,x.val))⁻¹) :
    (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G := by
  let F := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  obtain ⟨N,hN,hn,hgn⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData G)
  have hFG : ∀ x : UnitSphere,
      (coefficientSmoothData F).1 x.val * (coefficientSmoothData G).1 x.val = 1 := by
    intro x
    change coefficientValue 2 F x.val * coefficientValue 2 G x.val = 1
    rw [coefficientValue_referenceGaugeNormalCoefficientJetsFamily,hG x]
    exact mul_inv_cancel₀ (ne_of_gt
      (referenceGaugeNormalCoefficient_sphere_pos g L Φ a y0 B ε C ρ H w hData p x))
  have hProd : (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2 : ℝ))) := by
    unfold referenceGaugeNormalNegativeHalfMultiplierFamily
    change (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp _ = _
    rw [nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hgm,
      nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 G hN hn hgn]
    exact nativeNegativeHalfSmoothMulL_comp_eq_id_of_sphere_mul_eq_one hF hO hD τ0
      (coefficientSmoothData F) (coefficientSmoothData G) hM hN hm hgm hn hgn hFG
  have hi := (referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).2
  apply ContinuousLinearMap.ext
  intro u
  have hp := congrArg
    (fun T : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T u) hProd
  change referenceGaugeNormalNegativeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 G u) = u at hp
  exact (congrArg (referenceGaugeNormalNegativeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse hp).symm.trans
    (hi.inverse_apply_self _)

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalHalfMultiplier_inverse_eq_native_reciprocal
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalNegativeMultiplier_inverse_eq_native_reciprocal
