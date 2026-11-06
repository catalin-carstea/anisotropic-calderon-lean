import Calderon.ActualReferenceGaugeNormalMultiplierInverse
import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.NativeHalfCoefficientInverseCompatibility
import Calderon.InversePairingTransport

/-! Full upfront: actual-gauge-boundary-jets-author-oct15-v001/
EXPANSION-reciprocal-compatibility-v005.md. SAME reciprocal normal multipliers,
actual pivot pairing and actual half/negative-half inclusion. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

theorem sphereSobolevDualPairing_referenceGaugeNormalMultiplier
    (p : ℝ × (R3 × ℝ))
    (u : SphereSobolev (-(1/2 : ℝ))) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceGaugeNormalNegativeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p u) v =
    sphereSobolevDualPairing (-(1/2 : ℝ)) u
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p v) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) v u

attribute [local irreducible] referenceGaugeNormalHalfMultiplierFamily
  referenceGaugeNormalNegativeHalfMultiplierFamily ContinuousLinearMap.inverse
  referenceGaugeNormalCoefficientJetsFamily sphereSobolevDualPairing sphereSobolevInclusionL
  NativeCoefficientBoundaryMultiplier.nativeHalfCoefficientMulL
  NativeCoefficientBoundaryMultiplier.nativeNegativeHalfCoefficientMulL

theorem sphereSobolevDualPairing_referenceGaugeNormalMultiplier_inverse
    (p : ℝ × (R3 × ℝ))
    (u : SphereSobolev (-(1/2 : ℝ))) (v : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      ((referenceGaugeNormalNegativeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse u) v =
    sphereSobolevDualPairing (-(1/2 : ℝ)) u
      ((referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse v) := by
  let P : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let N : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hi := referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  exact pairing_inverse_eq_of_forward_pairing
    (sphereSobolevDualPairing (-(1/2 : ℝ))) P N P.inverse N.inverse
    hi.1.self_apply_inverse hi.2.self_apply_inverse
    (sphereSobolevDualPairing_referenceGaugeNormalMultiplier
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) u v

theorem referenceGaugeNormalMultiplier_inverse_half_negative_compatibility
    (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceGaugeNormalHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
    (referenceGaugeNormalNegativeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse.comp
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let P : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceGaugeNormalHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let N : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceGaugeNormalNegativeHalfMultiplierFamily g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hi := referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hLink : J.comp P = N.comp J := by
    dsimp only [J,P,N]
    unfold referenceGaugeNormalHalfMultiplierFamily referenceGaugeNormalNegativeHalfMultiplierFamily
    exact nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)
  exact NativeHalfCoefficientInverseCompatibility.inverse_comp_intertwiner_of_comp_eq P N J
    hi.1 hi.2 hLink

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.sphereSobolevDualPairing_referenceGaugeNormalMultiplier
#print axioms OAI.AnisotropicCalderon.ConnectionError.sphereSobolevDualPairing_referenceGaugeNormalMultiplier_inverse
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalMultiplier_inverse_half_negative_compatibility
