import Calderon.ActualReferenceRotationNormalHighJets
import Calderon.NativeHalfCoefficientInverseCompatibility
import Calderon.NativeThreeHalfCoefficientMultiplierInverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  NativeThreeHalfCoefficientMultiplierInverse NativeCoefficientBoundaryMultiplier
  NativeHalfCoefficientInverseCompatibility
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceRotationNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t)

lemma contDiff_referenceRotationNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction (coordinateRotationPrincipalFamily i j a)) (contDiff_normalCoefficientFunction (coordinateRotationPrincipalFamily i j a)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support (coordinateRotationPrincipalFamily i j a) (closedBall (0 : R3) 3)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2)

lemma referenceRotationNormalThreeHalfMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    (referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).IsInvertible :=
  nativeThreeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t)
    (referenceRotationNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData i j t)

lemma contDiff_referenceRotationNormalThreeHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      (referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (referenceRotationNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j t).contDiffAt_map_inverse.comp t
      (contDiff_referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j).contDiffAt

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3)

def referenceRotationNormalHalfMultiplierFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)

lemma contDiff_referenceRotationNormalHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction (coordinateRotationPrincipalFamily i j a))
    (NativeBoundaryCoefficientFamilies.contDiff_normalCoefficientFunction (coordinateRotationPrincipalFamily i j a)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction_support (coordinateRotationPrincipalFamily i j a) (closedBall (0 : R3) 3)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2)

lemma referenceRotationNormalHalfMultiplierFamily_isInvertible (t : ℝ × (ℝ × (R3 × ℝ))) :
    (referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).IsInvertible := by
  apply nativeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
  intro x
  have hValue := congrFun
    (coefficientValue_referenceRotationNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData i j t) x.val
  exact lt_of_lt_of_eq
    (referenceRotationNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData i j t x) hValue

lemma contDiff_referenceRotationNormalHalfMultiplierFamily_inverse :
    ContDiff ℝ ∞ (fun t : ℝ × (ℝ × (R3 × ℝ)) =>
      (referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (referenceRotationNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j t).contDiffAt_map_inverse.comp t
      (contDiff_referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j).contDiffAt

lemma referenceRotationNormalMultiplier_inverse_high_half_compatibility (t : ℝ × (ℝ × (R3 × ℝ))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceRotationNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse =
    (referenceRotationNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t).inverse.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  inverse_comp_intertwiner_of_comp_eq _ _ _
    (referenceRotationNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t)
    (referenceRotationNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_referenceRotationNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData i j t))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalThreeHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalThreeHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalMultiplier_inverse_high_half_compatibility
