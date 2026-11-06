import Calderon.ActualReferenceGaugeNormalMultiplierInverse
import Calderon.NativeThreeHalfCoefficientMultiplierInverse
import Calderon.SphereSobolevTangentialEndpointCompatibility

/-! Same actual gauge alpha, native high multiplier, and exact reciprocal
inclusion to the half endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  MetricVolume SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeThreeHalfCoefficientMultiplierInverse
  NativeOrderOneCoefficientMultiplier

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (y0 : R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeNormalThreeHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p)

theorem contDiff_referenceGaugeNormalThreeHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceGaugeNormalThreeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficient g L Φ a)
    (contDiff_referenceGaugeNormalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugeNormalCoefficient_support g L Φ y0 B ε C ρ H a w hData)

theorem referenceGaugeNormalThreeHalfMultiplierFamily_isInvertible
    (p : ℝ × (R3 × ℝ)) :
    (referenceGaugeNormalThreeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).IsInvertible := by
  apply nativeThreeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p)
  intro x
  rw [coefficientValue_referenceGaugeNormalCoefficientJetsFamily]
  exact referenceGaugeNormalCoefficient_sphere_pos g L Φ a y0 B ε C ρ H w hData p x

theorem contDiff_referenceGaugeNormalThreeHalfMultiplierFamily_inverse :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceGaugeNormalThreeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceGaugeNormalThreeHalfMultiplierFamily_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).contDiffAt_map_inverse.comp p
      (contDiff_referenceGaugeNormalThreeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt

attribute [local irreducible] referenceGaugeNormalThreeHalfMultiplierFamily
  referenceGaugeNormalHalfMultiplierFamily nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL

theorem referenceGaugeNormalThreeHalfMultiplierFamily_half_inclusion
    (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceGaugeNormalThreeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) =
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let Q3 := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p
  let Q2 := referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p
  have hValue : coefficientValue 3 Q3 = coefficientValue 2 Q2 := by
    funext z
    exact (coefficientValue_referenceGaugeNormalCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg 3 p z).trans
        (coefficientValue_referenceGaugeNormalCoefficientJetsFamily
          g L Φ y0 B ε C ρ H a w hData hg 2 p z).symm
  unfold referenceGaugeNormalThreeHalfMultiplierFamily referenceGaugeNormalHalfMultiplierFamily
  exact nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q3 Q2 hValue

theorem referenceGaugeNormalThreeHalfMultiplierFamily_inverse_half_inclusion
    (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceGaugeNormalThreeHalfMultiplierFamily
        g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse =
    (referenceGaugeNormalHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse.comp
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let P3 := referenceGaugeNormalThreeHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let P := referenceGaugeNormalHalfMultiplierFamily
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hHigh := referenceGaugeNormalThreeHalfMultiplierFamily_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  have hHalf := (referenceGaugeNormalMultiplierFamilies_isInvertible
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).1
  have hLink := referenceGaugeNormalThreeHalfMultiplierFamily_half_inclusion
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  apply ContinuousLinearMap.ext
  intro u
  have hPoint := congrArg
    (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => T (P3.inverse u)) hLink
  change I (P3 (P3.inverse u)) = P (I (P3.inverse u)) at hPoint
  rw [hHigh.self_apply_inverse] at hPoint
  have hInv := congrArg (fun v : SphereSobolev (1/2 : ℝ) => P.inverse v) hPoint
  rw [hHalf.inverse_apply_self] at hInv
  exact hInv.symm

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalThreeHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceGaugeNormalThreeHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalThreeHalfMultiplierFamily_half_inclusion
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceGaugeNormalThreeHalfMultiplierFamily_inverse_half_inclusion
