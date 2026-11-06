import Calderon.NativeFiveHalfCoefficientMultiplierTopology
import Calderon.ActualReferenceNormalThreeHalfInverseFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  NativeThreeHalfCoefficientMultiplierInverse
  NativeFiveHalfCoefficientMultiplier NativeFiveHalfCoefficientMultiplierInverse NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNormalCoefficientJetsFamily4 : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 4 :=
  commonSupportCoefficientFamily 4 (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma coefficientValue_referenceNormalCoefficientJetsFamily4_eq (p : ℝ × (R3 × ℝ)) :
    coefficientValue 4 (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p) =
      coefficientValue 3 (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p) :=
  coefficientValue_commonSupportCoefficientFamily_order_eq 4 3 (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1) p

lemma referenceNormalCoefficientJetsFamily4_sphere_pos (p : ℝ × (R3 × ℝ)) (x : UnitSphere) :
    0 < coefficientValue 4 (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p) x.1 := by
  rw [coefficientValue_referenceNormalCoefficientJetsFamily4_eq]
  exact referenceNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData p x

def referenceNormalFiveHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (5/2:ℝ) :=
  nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalFiveHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeFiveHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction a) (contDiff_normalCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1)

lemma referenceNormalFiveHalfMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible :=
  nativeFiveHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily4_sphere_pos g L y0 Φ B ε C ρ H a w hData p)

lemma contDiff_referenceNormalFiveHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceNormalFiveHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 p).contDiffAt_map_inverse.comp p
      (contDiff_referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0).contDiffAt

lemma sphereSobolevInclusionL_referenceNormalFiveHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p u) =
      referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) :=
  sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
    (coefficientValue_referenceNormalCoefficientJetsFamily4_eq g L y0 Φ B ε C ρ H a w hData p) u

lemma sphereSobolevInclusionL_referenceNormalFiveHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (referenceNormalFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse =
      (referenceNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).inverse.comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) :=
  sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL_inverse hcalc hF hO hD τ0
    (referenceNormalCoefficientJetsFamily4 g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData p)
    (coefficientValue_referenceNormalCoefficientJetsFamily4_eq g L y0 Φ B ε C ρ H a w hData p)
    (referenceNormalCoefficientJetsFamily4_sphere_pos g L y0 Φ B ε C ρ H a w hData p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
