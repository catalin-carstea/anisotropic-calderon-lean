import Calderon.ActualReferenceNormalThreeHalfInverseFamily
import Calderon.NativeHalfCoefficientInverseCompatibility
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeOrderOneCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeHalfCoefficientInverseCompatibility
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceNormalHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction a)
    (NativeBoundaryCoefficientFamilies.contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma referenceNormalHalfMultiplierFamily_isInvertible (p : ℝ × (R3 × ℝ)) :
    (referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible := by
  apply nativeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
  intro x
  have hValue := congrFun
    (coefficientValue_referenceNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData p) x.val
  exact lt_of_lt_of_eq
    (referenceNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData p x) hValue

lemma contDiff_referenceNormalHalfMultiplierFamily_inverse :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 p).contDiffAt_map_inverse.comp p
      (contDiff_referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0).contDiffAt

lemma referenceNormalMultiplier_inverse_high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse =
    (referenceNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  inverse_comp_intertwiner_of_comp_eq _ _ _
    (referenceNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (referenceNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_referenceNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData p))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalMultiplier_inverse_high_half_compatibility
