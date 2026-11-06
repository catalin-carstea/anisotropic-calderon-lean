import Calderon.ActualReferenceGaugeBoundaryCoefficientFamilies
import Calderon.ActualReferenceGaugeNativeEnergy
import Calderon.ActualReferenceRadialEndpointCompatibility
import Calderon.NativeH2ConormalRadialConversion
import Calderon.NativeH2ConormalTraceRepresentative

/-! Arbitrary native H2 inputs, the same weighted principal coefficient, and the
existing native normal/tangent conversion. No PDE premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeNegativeHalfSmoothMultiplier NativeFullSharpHalfTrace

theorem ordinaryConormalTraceL_scalar_principal
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (m : SmoothData) (F G : SmoothCoefficientMatrix 2)
    (hFG : coefficientMatrixField 2 G = fun z => m.1 z • coefficientMatrixField 2 F z)
    (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 G U =
      sphereContinuousScalarMulL (smoothSphereValue m) (ordinaryConormalTraceL hcalc τ0 F U) := by
  apply Lp.ext
  filter_upwards [ordinaryConormalTraceL_value_ae hcalc τ0 G U,
    ordinaryConormalTraceL_value_ae hcalc τ0 F U,
    sphereContinuousScalarMul_value_ae (smoothSphereValue m) (ordinaryConormalTraceL hcalc τ0 F U)]
    with x hG hF hMul
  change ordinaryConormalTraceL hcalc τ0 G U x =
    sphereContinuousScalarMul (smoothSphereValue m) (ordinaryConormalTraceL hcalc τ0 F U) x
  rw [hG,hMul,hF,hFG]
  change (∑ i : Fin 3, ∑ j : Fin 3,
      x.val i*(m.1 x.val • coefficientMatrixField 2 F x.val) i j*
        strongCoordinateTraceL hcalc τ0 j U x) =
    m.1 x.val*(∑ i : Fin 3, ∑ j : Fin 3,
      x.val i*coefficientMatrixField 2 F x.val i j*strongCoordinateTraceL hcalc τ0 j U x)
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg

def referenceGaugePrincipalJetsFamily (n : ℕ) :
    (ℝ × (R3 × ℝ)) → SmoothCoefficientMatrix n :=
  commonSupportMatrixFamily n (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData)

theorem coefficientMatrixField_referenceGaugePrincipalJetsFamily
    (n : ℕ) (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField n (referenceGaugePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData hg n p) =
      fun z => referenceGaugePrincipalCoefficient g L Φ a (p,z) :=
  coefficientMatrixField_commonSupportMatrixFamily n (referenceGaugePrincipalCoefficient g L Φ a)
    (contDiff_referenceGaugePrincipalCoefficient g L Φ y0 B ε C ρ H a w hData hg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceGaugePrincipalCoefficient_support g L Φ y0 B ε C ρ H a w hData) p

theorem referenceGaugePrincipalJetsFamily_normal_data (p : ℝ × (R3 × ℝ)) :
    coefficientSmoothData
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p) =
    boundaryNormalCoefficientData
      (referenceGaugePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 p) :=
  coefficientSmoothData_referenceGaugeNormalCoefficientJetsFamily
    g L Φ y0 B ε C ρ H a w hData hg p

theorem referenceGaugePrincipalJetsFamily_tangent_data
    (p : ℝ × (R3 × ℝ)) (j : Fin 3) :
    coefficientSmoothData
      (referenceGaugeTangentCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 j p) =
    boundaryTangentCoefficientData
      (referenceGaugePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 p) j :=
  coefficientSmoothData_referenceGaugeTangentCoefficientJetsFamily
    g L Φ y0 B ε C ρ H a w hData hg j p

def referenceGaugeConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) :
    BallSobolev 2 →L[ℝ] SphereL2 :=
  ordinaryConormalTraceL hcalc τ0
    (referenceGaugePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 p)

theorem referenceGaugeConormalTraceFamily_eq_weighted_original
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) :
    referenceGaugeConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 p U =
    sphereContinuousScalarMulL
      (smoothSphereValue (referenceExponentialGaugeData g L y0 Φ B ε C ρ H a w hData hg p))
      (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 U) := by
  rw [referenceConormalTraceFamily_joint_coefficient_eq
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 p]
  apply ordinaryConormalTraceL_scalar_principal
  rw [coefficientMatrixField_referenceGaugePrincipalJetsFamily,
    coefficientMatrixField_commonSupportMatrixFamily]
  rfl

attribute [local irreducible] referenceGaugeConormalTraceFamily
  referenceGaugePrincipalJetsFamily referenceGaugeNormalCoefficientJetsFamily
  referenceGaugeTangentCoefficientJetsFamily nativeNegativeHalfCoefficientMulL
  ordinaryConormalTraceL outwardRadialTraceL nativeHalfTraceL


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_scalar_principal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugePrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceGaugePrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugePrincipalJetsFamily_normal_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugePrincipalJetsFamily_tangent_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeConormalTraceFamily_eq_weighted_original
