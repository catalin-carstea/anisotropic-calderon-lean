import Calderon.SphereSobolevDualOrthogonalPullback
import Calderon.ActualReferenceGaugeConormalGreen
import Calderon.ActualReferenceGaugeTangentEndpoint
import Calderon.ActualReferenceGaugeConormalFlux
import Calderon.ActualReferenceGaugeConormalRadialConversion
import Calderon.ActualReferenceRadialInvertibleEndpointCompatibility
import Calderon.SphereSobolevDenseEndpointCovariance

/-! Full upfront: actual-gradient-drift-author-oct15-v001/
EXPANSION-actual-gauge-radial-decomposition-v010.md. SAME original solves and radial endpoint. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion NativeHarmonicHalfCoarseDualPairing
  NativeFullSharpHalfTrace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceGaugeWeakConormalEndpointFamily referenceGaugeConormalTraceFamily
  referenceHarmonicLiftFamily referenceWeakHalfLiftFamily referenceLowerRadialEndpointFamily
  referenceGaugeNormalCoefficientJetsFamily referenceGaugeTangentCoefficientJetsFamily
  referenceGaugeTangentEndpointFamily nativeHalfTraceL harmonicLiftCompletion
  harmonicFirstOrderLiftCompletion sphereSobolevInclusionL sphereSobolevZeroEquiv


theorem referenceGaugeWeakConormalEndpointFamily_eq_flux
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceGaugeConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 p
          (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
            (harmonicLiftCompletion hF f)))) := by
  apply sphereSobolev_eq_of_dualPairing_eq (1/2 : ℝ)
  intro z
  have hG := sphereSobolevDualPairing_referenceGaugeWeakConormal_high_flux
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO τ0 p.1 p.2 hStrong hWeak f z
  have hFluxGraph := referenceGaugeConormalTraceFamily_eq_weighted_original
    g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 p
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
      (harmonicLiftCompletion hF f))
  have hP := congrArg (fun b : SphereL2 =>
    inner ℝ b (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z))) hFluxGraph
  exact hG.trans (hP.symm.trans
    (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 z _).symm)

theorem referenceGaugeWeakConormalEndpointFamily_eq_normal_add_tangent
    (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p =
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)).comp
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) +
    referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let A := referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let M := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 2 p)
  let T := referenceGaugeTangentEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p
  let N := referenceGaugeWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF p
  apply ContinuousLinearMap.ext
  intro f
  apply denseRange_clm_apply_eq I
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) N (M.comp A+T)
  intro u
  let U : BallSobolev 2 := referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
    (harmonicLiftCompletion hF u)
  have hTrace := nativeHalfTraceL_firstOrder_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong u
  have hRad := referenceLowerRadialEndpointFamily_inclusion_eq_coarse_radial_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hNormal hStrong hWeak u
  have hFlux := referenceGaugeConormalTraceFamily_negativeHalf_eq_normal_add_tangent
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p U
  have hEq := referenceGaugeWeakConormalEndpointFamily_eq_flux
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hStrong hWeak u
  have hT : T (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) = T (I u) :=
    congrArg T hTrace
  have hM : M (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U))) = M (A (I u)) :=
    congrArg M hRad.symm
  change N (I u) = M (A (I u))+T (I u)
  have hFlux' : sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD
        (referenceGaugeConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hg hcalc τ0 p U)) =
      M (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (outwardRadialTraceL hcalc τ0 U))) +
      T (nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1 U)) := by
    simpa only [T,referenceGaugeTangentEndpointFamily,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply] using hFlux
  exact hEq.trans (hFlux'.trans
    (congrArg₂ (fun x y : SphereSobolev (-(1/2 : ℝ)) => x+y) hM hT))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeWeakConormalEndpointFamily_eq_flux
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeWeakConormalEndpointFamily_eq_normal_add_tangent
