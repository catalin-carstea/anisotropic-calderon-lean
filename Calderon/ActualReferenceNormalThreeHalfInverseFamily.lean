import Calderon.ActualReferenceNormalOrderOneFamily
import Calderon.NativeThreeHalfCoefficientMultiplierInverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  NativeThreeHalfCoefficientMultiplierInverse
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma referenceNormalThreeHalfMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible :=
  nativeThreeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalThreeHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 p).contDiffAt_map_inverse.comp p
      (contDiff_referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0).contDiffAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalThreeHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalThreeHalfMultiplierFamily_inverse
