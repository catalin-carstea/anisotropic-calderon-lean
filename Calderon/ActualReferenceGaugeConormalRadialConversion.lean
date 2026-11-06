import Calderon.ActualReferenceGaugeConormalFlux
import Calderon.NativeH2ConormalCoefficientRadialConversion

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeNegativeHalfSmoothMultiplier NativeFullSharpHalfTrace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)

include hData hg


attribute [local irreducible] referenceGaugeConormalTraceFamily
  referenceGaugePrincipalJetsFamily referenceGaugeNormalCoefficientJetsFamily
  referenceGaugeTangentCoefficientJetsFamily nativeNegativeHalfCoefficientMulL
  ordinaryConormalTraceL outwardRadialTraceL nativeHalfTraceL

theorem referenceGaugeConormalTraceFamily_negativeHalf_eq_normal_add_tangent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) :
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceGaugeConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 p U)) =
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U))) +
    ∑ j : Fin 3,
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceGaugeTangentCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 j p)
        (sphereTangentialDerivativeL hF hO hD j
          (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U))) := by
  unfold referenceGaugeConormalTraceFamily
  exact nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    hcalc hF hO hD τ0
    (referenceGaugePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData hg 2 p)
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)
    (fun j => referenceGaugeTangentCoefficientJetsFamily
      g L Φ y0 B ε C ρ H a w hData hg 2 j p)
    (referenceGaugePrincipalJetsFamily_normal_data g L y0 Φ B ε C ρ H a w hData hg p)
    (referenceGaugePrincipalJetsFamily_tangent_data g L y0 Φ B ε C ρ H a w hData hg p) U

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeConormalTraceFamily_negativeHalf_eq_normal_add_tangent
