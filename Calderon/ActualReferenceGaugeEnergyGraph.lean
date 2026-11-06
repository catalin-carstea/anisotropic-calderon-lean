import Calderon.NativeReciprocalGaugeMultipliers
import Calderon.NativeGaugeTestProductEnergy
import Calderon.ActualReferenceGaugeScalarMultipliers
import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
import Calderon.NativeSmoothOperatorRealization
import Calderon.ActualReferenceWeakEnergyApply
import Calderon.BilinearRotationInvertibility
import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceStrongEnergy
import Calderon.DirichletForcingInjectivity
import Calderon.ActualReferenceWeakDirichletEvaluationReference

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
theorem referenceWeightedDrift_pairing_eq_native_depth
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (v : R3) :
    inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) v =
      -L * fderiv ℝ (referenceRescaledDepth g L Φ (q,(y,r))) z
        (matrixOperatorMap (a ((q,(y,r)),z)) v) := by
  let u : R3 → ℝ := InnerProductSpace.toDual ℝ R3 v
  have hgrad : gradient u z = v := by
    apply ext_inner_right ℝ
    intro V
    rw [inner_gradient_left]
    exact congrArg (fun f : R3 →L[ℝ] ℝ => f V)
      ((InnerProductSpace.toDual ℝ R3 v).fderiv)
  have hPair := referenceRescaledWeightedDrift_pairing g L Φ H w hg y0 B ε C ρ a hData
    q hq y hy r hr z hz u
  rw [hgrad] at hPair
  have hDataCopy := hData
  rcases hDataCopy with ⟨hPositive,_,_,_,hA,_,_,_,_,_,_,_,_,_⟩
  rcases hPositive with ⟨_,_,_,_,_,_,_,_,_,_,_,hLocal,_,_,_⟩
  have hLocalz := hLocal q hq y hy r hr z hz
  have hVol : vol (fun x => H ((q,(y,r)),x)) z = w ((q,(y,r)),z) := by
    change Real.sqrt (H ((q,(y,r)),z)).det = _
    rw [hLocalz.1]
    exact hLocalz.2.2.symm
  have hFlux : referenceRescaledFlux H (q,(y,r)) u z =
      matrixOperatorMap (a ((q,(y,r)),z)) v := by
    rw [hA]
    simp only [referenceRescaledFlux,metricDivergenceFlux,principalCoefficient,hVol,
      map_smul,ContinuousLinearMap.smul_apply,hgrad]
  rw [hFlux] at hPair
  exact hPair

include hg hData in
theorem referenceGaugeInverseMultiplier_gradient_pairing
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ (ballOpens : Set R3))
    (v : R3) :
    TauCeti.PDE.matrixBilinearForm
      (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),z))
      (gradient (coefficientValue 2
        (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-L) (q,(y,r)))) z) v =
      inner ℝ (conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) v := by
  let p : ℝ × (R3 × ℝ) := (q,(y,r))
  let t := referenceRescaledDepth g L Φ p
  let F := referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-L) p
  have hNear : coefficientValue 2 F =ᶠ[𝓝 z] (fun x => Real.exp (-L*t x)) := by
    filter_upwards [ballOpens.isOpen.mem_nhds hz] with x hx
    exact coefficientValue_referenceGaugeScalarJets_on_unitBall
      g hg L y0 Φ B ε C ρ H a w hData 2 (-L) p x hx
  have hFD : fderiv ℝ (coefficientValue 2 F) z =
      Real.exp (-L*t z) • (-L • fderiv ℝ t z) :=
    hNear.fderiv_eq.trans
      ((((contDiff_referenceRescaledDepth_slice g hg L y0 Φ B ε C ρ H a w hData p).differentiable
        (by simp)) z).hasFDerivAt.const_mul (-L)).exp.fderiv
  have hBall : z ∈ closedBall (0 : R3) 2 := by
    apply closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)
    exact ball_subset_closedBall hz
  rw [matrixBilinearForm_eq_inner_matrixOperatorMap,inner_gradient_left,hFD,
    referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
      g L y0 Φ B ε C ρ H a w hData,map_smul,ContinuousLinearMap.smul_apply]
  simp only [ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul]
  have hPair := referenceWeightedDrift_pairing_eq_native_depth g hg L y0 Φ B ε C ρ H a w hData
    q hq y hy r hr z hBall v
  rw [hPair]
  change Real.exp (-L*t z) * (Real.exp (L*t z) * (-L *
    fderiv ℝ t z (matrixOperatorMap (a (p,z)) v))) =
    -L * fderiv ℝ t z (matrixOperatorMap (a (p,z)) v)
  have he : Real.exp (-L*t z)*Real.exp (L*t z) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [← mul_assoc,he,one_mul]

include hg hData in
theorem referenceWeakEnergyFamily_eq_gauge_principal_test_product
    (hcalc : FixedSobolevCalculus)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : BallH1) (v : BallH1Zero) :
    referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,r)) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) 0 0
        u (nativeCoefficientZeroProductL hcalc
          (referenceGaugeScalarJets g hg L y0 Φ B ε C ρ H a w hData 2 (-L) (q,(y,r))) v : BallH1) := by
  rw [referenceWeakEnergyFamily_apply]
  rw [nativeCoefficientZeroProductL_coe]
  symm
  apply energyFormH1_nativeCoefficient_test_product
  · intro z hz
    rw [coefficientValue_referenceGaugeScalarJets_on_unitBall
      g hg L y0 Φ B ε C ρ H a w hData 2 (-L) (q,(y,r)) z hz,
      referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
        g L y0 Φ B ε C ρ H a w hData,smul_smul]
    have he : Real.exp (-L*referenceRescaledDepth g L Φ (q,(y,r)) z)*
        Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    rw [he,one_smul]
  · exact referenceGaugeInverseMultiplier_gradient_pairing
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr

end OAI.AnisotropicCalderon.ConnectionError
