import Calderon.ActualReferenceRotationAdjointHighWeakCoherence
import Calderon.ActualReferenceRotationAdjointLowConormalFamily
import Calderon.ActualReferenceRotationAdjointSharpConormalFamily
import Calderon.ActualReferenceRotationAdjointH2FullGreen
import Calderon.NativeSupportedAdjointConormalGraph

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
  NativePolynomialBulkMoments NativeSmoothSharpTraceCompletion NativeHalfCoefficientConormalTrace
  NativeHarmonicHalfCoarseDualPairing
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma sphereSobolevDualPairing_referenceRotationAdjointWeakConormal_high_eq_coarse
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) =
      ⟪ordinaryConormalTraceL hcalc τ0
          (nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
          (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f),
        τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF z)⟫_ℝ := by
  let q := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  have hU := (referenceRotationAdjointH2LiftFamily_highWeakCoherence g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg hF hO i j t hOriginal f).trans
      (referenceRotationAdjointWeakHalfLiftFamily_eq_native g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hF i j t hOriginal q)
  have hPair := sphereSobolevDualPairing_nativeWeakConormalEndpoint (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    (memLp_referenceRotationAdjointEnergyIntegrand g L y0 Φ B ε C ρ H a w hData i j t) hF q z
  have hCo := congrArg (fun u : BallH1 => sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
    (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
    u (harmonicFirstOrderLiftCompletion hF z)) hU.symm
  exact (hPair.trans hCo).trans
    (nativeNormalizedGreenPairing sphereSurfaceMass _ _ sphereSurfaceMass_pos
      (referenceRotationAdjointH2LiftFamily_full_test_energy_Green g L y0 Φ B ε C ρ H a w hData
        τ0 hcalc hreg hF i j t hOriginal f (harmonicFirstOrderLiftCompletion hF z)))

lemma referenceRotationAdjointWeakConormalEndpointFamily_high_eq_coarse
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0
          (nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
          (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f))) := by
  apply ext_inner_left ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ) z _ = sphereSobolevDualPairing (1/2:ℝ) z _
  exact (sphereSobolevDualPairing_referenceRotationAdjointWeakConormal_high_eq_coarse
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF hO i j t hOriginal f z).trans
      (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 z _).symm

lemma referenceRotationAdjointConormalEndpointFamily_high_half_compatibility
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (referenceRotationAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t) =
      (referenceRotationAdjointWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hF i j t).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  let F := nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)
  let U := referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f
  let b := nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U
  have hEval : referenceRotationAdjointHighConormalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j t f=b := rfl
  have hZero := sphereSobolevInclusionL_nativeHalfCoefficientConormalTraceL hF hO hD hcalc τ0 F U
  have hIncl := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) hZero
  have hTrans := congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A b)
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  have hHigh := congrArg (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) hEval
  have hCoarse := referenceRotationAdjointWeakConormalEndpointFamily_high_eq_coarse
    g L y0 Φ B ε C ρ H a w hData τ0 hcalc hreg hF hO hD i j t hOriginal f
  exact hHigh.trans (hTrans.symm.trans (hIncl.trans hCoarse.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationAdjointWeakConormal_high_eq_coarse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointWeakConormalEndpointFamily_high_eq_coarse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointConormalEndpointFamily_high_half_compatibility
