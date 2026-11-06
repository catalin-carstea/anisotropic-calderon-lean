import Calderon.ActualReferenceTwoAngleGreenCompatibility
import Calderon.ActualReferenceTwoAngleLowerRadialEndpointCore
import Calderon.ActualReferenceRotationRadialCompatibility

/-! Genuine SAME upper/lower DN graph. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


open NativePolynomialBulkMoments NativeHarmonicHalfCoarseDualPairing
  NativeFullSharpHalfTrace NativeHalfTraceRightInverse

open NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies

lemma referenceTwoAngleLowerRadialEndpointFamily_inclusion_eq_coarse_radial
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.2.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceTwoAngleLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD
      (outwardRadialTraceL hcalc τ0 (referenceTwoAngleHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f)))) := by
  have hb := nativeHalfTraceL_firstOrder_referenceTwoAngleHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hStrong f
  have hc := referenceTwoAngleWeakConormalEndpointFamily_eq_conormal_of_original
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hWeak hStrong f
  have hn := referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t.1 t.2.1 t.2.2 hNormal
  rw [referenceTwoAngleLowerRadialEndpointFamily_apply]
  exact nativeCoefficient_boundary_radial_conversion_of_isInvertible hcalc hF hO hD τ0
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
    (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)
    (fun d => referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l d t)
    (coefficientSmoothData_referenceTwoAngleNormalJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j k l t)
    (fun d => coefficientSmoothData_referenceTwoAngleTangentJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j k l d t) hn _ _ _ hb hc

lemma referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.2.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceTwoAngleSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) =
    (referenceTwoAngleLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hc := referenceTwoAngleLowerRadialEndpointFamily_inclusion_eq_coarse_radial
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hNormal hWeak hStrong f
  have ho := nativeHalfOutwardTraceL_negative_inclusion hcalc hF hO hD τ0
    (referenceTwoAngleHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f))
  exact ho.trans hc.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleLowerRadialEndpointFamily_inclusion_eq_coarse_radial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
