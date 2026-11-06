import Calderon.ActualReferenceTwoAngleNormalHighJets
import Calderon.NativeHalfCoefficientInverseCompatibility
import Calderon.NativeThreeHalfCoefficientMultiplierInverse

/-! Exact native rotation endpoint inverse specialization; full upfront v079. -/
set_option autoImplicit false
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

def referenceTwoAngleNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t)

lemma contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l)) (contDiff_normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support (referenceTwoAnglePrincipalFamily a i j k l) (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2)

lemma referenceTwoAngleNormalThreeHalfMultiplierFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).IsInvertible :=
  nativeThreeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
    (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t)
    (referenceTwoAngleNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData i j k l t)

lemma contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (fun t : ℝ × (ℝ × (ℝ × (R3 × ℝ))) =>
      (referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (referenceTwoAngleNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t).contDiffAt_map_inverse.comp t
      (contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j k l).contDiffAt

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)

def referenceTwoAngleNormalHalfMultiplierFamily (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)

lemma contDiff_referenceTwoAngleNormalHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l))
    (NativeBoundaryCoefficientFamilies.contDiff_normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (NativeBoundaryCoefficientFamilies.normalCoefficientFunction_support (referenceTwoAnglePrincipalFamily a i j k l) (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2)

lemma referenceTwoAngleNormalHalfMultiplierFamily_isInvertible (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).IsInvertible := by
  apply nativeHalfCoefficientMulL_isInvertible_of_pos hcalc hF hO hD τ0
  intro x
  have hValue := congrFun
    (coefficientValue_referenceTwoAngleNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData i j k l t) x.val
  exact lt_of_lt_of_eq
    (referenceTwoAngleNormalCoefficientJetsFamily3_sphere_pos g L y0 Φ B ε C ρ H a w hData i j k l t x) hValue

lemma contDiff_referenceTwoAngleNormalHalfMultiplierFamily_inverse :
    ContDiff ℝ ∞ (fun t : ℝ × (ℝ × (ℝ × (R3 × ℝ))) =>
      (referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (referenceTwoAngleNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t).contDiffAt_map_inverse.comp t
      (contDiff_referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j k l).contDiffAt

lemma referenceTwoAngleNormalMultiplier_inverse_high_half_compatibility (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceTwoAngleNormalThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse =
    (referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  inverse_comp_intertwiner_of_comp_eq _ _ _
    (referenceTwoAngleNormalThreeHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
    (referenceTwoAngleNormalHalfMultiplierFamily_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_referenceTwoAngleNormalCoefficientJetsFamily3_eq g L y0 Φ B ε C ρ H a w hData i j k l t))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalThreeHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalThreeHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalHalfMultiplierFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleNormalHalfMultiplierFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalMultiplier_inverse_high_half_compatibility
