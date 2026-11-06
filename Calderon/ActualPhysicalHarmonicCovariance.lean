import Calderon.ActualPhysicalMetricNormalization
import Calderon.MetricPullbackDivergence
import Calderon.ActualNativeSmoothOperatorRealization
import Calderon.ActualPhysicalBoundaryChainRule
/-! Actual physical/native harmonic covariance. No covariance/kernel/Psi
premise is introduced. Ambient smooth-data scope is explicit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem referenceRescaledPositiveExpression_physical_pullback_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0) (u : SmoothData)
    (z : R3) (hz : z ∈ (ballOpens : Set R3)) :
    referenceRescaledPositiveExpression g L Φ H w (q,(y,r))
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u).1 z =
      (r^2 * |(operatorMatrixMap (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))).det| *
        Real.exp (-L*referenceRescaledDepth g L Φ (q,(y,r)) z)) *
      (-coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))) := by
  let X : R3 → R3 := fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))
  let t := referenceRescaledDepth g L Φ (q,(y,r))
  let v := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u
  let K := conformalMatrix (fun x => H ((q,(y,r)),x)) (fun x => L*t x)
  let G := conformalMatrix (fun x => H ((q,(y,r)),x)) (fun x => Real.log |r| + L*t x)
  let J := referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id))
  have ht : ContDiff ℝ ∞ t := contDiff_conformalReferenceCoordinateDepth.comp hX
  have hPositive := hData.1
  rcases hPositive with ⟨_,_,_,_,_,_,hH,hPos,_,_,_,_,_,_,_⟩
  have hHs : ContDiff ℝ ∞ (fun x => H ((q,(y,r)),x)) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  have hKentries (i j : Fin 3) : ContDiff ℝ ∞ (fun x => K x i j) :=
    conformalMatrix_smooth_entries _ _
      (fun i j => contDiff_pi.mp (contDiff_pi.mp hHs i) j) (contDiff_const.mul ht) i j
  have hKpos (x : R3) : (K x).PosDef :=
    conformalMatrix_posDef _ _ (fun x => hPos ((q,(y,r)),x)) x
  have hZK : ContDiff ℝ ∞ (metricDivergenceFlux K v.1) :=
    contDiff_metricDivergenceFlux K hKentries hKpos v.1 v.2
  have hz2 : z ∈ closedBall (0 : R3) 2 := by
    change dist z (0 : R3) < 1 at hz
    change dist z (0 : R3) ≤ 2
    linarith
  have hJ := coordinateJacobianMatrix_referencePhysicalEndpoint_isUnit_det
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 z hz2
  have hCov := coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
    (fun x => g (q • x))
    (fun i j => (hg.smooth i j).comp
      ((q • (ContinuousLinearMap.id ℝ R3)).contDiff))
    (fun x => hg.posDef (q • x)) X u.1 hX u.2 z hJ
  change coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric (fun x => g (q • x)) X) v.1) z =
    |(coordinateJacobianMatrix X z).det| *
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) (X z) at hCov
  have hLocalDiv : coordinateFluxDivergence
      (metricDivergenceFlux (pullbackMetric (fun x => g (q • x)) X) v.1) z =
      coordinateFluxDivergence (metricDivergenceFlux G v.1) z := by
    have hFlux : metricDivergenceFlux (pullbackMetric (fun x => g (q • x)) X) v.1 =ᶠ[𝓝 z]
        metricDivergenceFlux G v.1 := by
      filter_upwards [ballOpens.isOpen.mem_nhds hz] with x hx
      have hx2 : x ∈ closedBall (0 : R3) 2 := by
        change dist x (0 : R3) < 1 at hx
        change dist x (0 : R3) ≤ 2
        linarith
      have hMetric : pullbackMetric (fun x => g (q • x)) X x = G x :=
        pullbackMetric_referenceOriginal_eq_conformal
          g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 x hx2
      change matrixOperatorMap (principalCoefficient (pullbackMetric (fun x => g (q • x)) X) x)
          (gradient v.1 x) = matrixOperatorMap (principalCoefficient G x) (gradient v.1 x)
      simp only [principalCoefficient,vol]
      rw [hMetric]
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hi : (fun x => metricDivergenceFlux (pullbackMetric (fun x => g (q • x)) X) v.1 x i) =ᶠ[𝓝 z]
        (fun x => metricDivergenceFlux G v.1 x i) :=
      hFlux.mono (fun x hx => congrArg (fun V : R3 => V i) hx)
    exact congrArg (fun F : R3 →L[ℝ] ℝ =>
      F (OAI.AnisotropicCalderon.NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq
  have hFluxScale : metricDivergenceFlux G v.1 =
      fun x => |r| • metricDivergenceFlux K v.1 x := by
    funext x
    simp only [G,K,metricDivergenceFlux,principalCoefficient_conformalMatrix _ _
      (fun x => hPos ((q,(y,r)),x)),map_smul,ContinuousLinearMap.smul_apply]
    rw [Real.exp_add,Real.exp_log (abs_pos.mpr hr0),smul_smul]
  have hScaleDiv : coordinateFluxDivergence (metricDivergenceFlux G v.1) z =
      |r| * coordinateFluxDivergence (metricDivergenceFlux K v.1) z := by
    have hc := coordinateFluxDivergence_exp_depth (fun _ : R3 => Real.log |r|)
      (metricDivergenceFlux K v.1) (-1) z (differentiableAt_const _) (hZK.differentiable (by simp) z)
    simp only [neg_neg,one_mul,Real.exp_log (abs_pos.mpr hr0),fderiv_const_apply,
      ContinuousLinearMap.zero_apply,mul_zero,sub_zero] at hc
    rw [hFluxScale]
    exact hc
  have hGauge := referenceRescaledConformalPositiveExpression_eq
    g L Φ H w hg y0 B ε C ρ a hData q hq y hy r hr z hz2 v.1 v.2
  change -coordinateFluxDivergence (metricDivergenceFlux K v.1) z =
    Real.exp (L*t z) * referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z at hGauge
  have hScaled : |r| * (Real.exp (L*t z) *
      referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z) =
      |(coordinateJacobianMatrix X z).det| *
        (-coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) (X z)) := by
    calc
      _ = |r| * (-coordinateFluxDivergence (metricDivergenceFlux K v.1) z) :=
        congrArg (fun A : ℝ => |r| * A) hGauge.symm
      _ = -coordinateFluxDivergence
          (metricDivergenceFlux (pullbackMetric (fun x => g (q • x)) X) v.1) z := by
        rw [hLocalDiv,hScaleDiv]
        ring
      _ = _ := by
        rw [hCov]
        ring
  have hDX : HasFDerivAt X (r • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun x => (Φ q x 1).1)
      (fun x => conformalReferenceGramFrameOperatorJoint g L (q,x))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r
  have hAeq : coordinateJacobianMatrix X z = r • operatorMatrixMap J := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap,hDX.fderiv,map_smul]
  have hDet : |(coordinateJacobianMatrix X z).det| = |r|^3 * |(operatorMatrixMap J).det| := by
    rw [hAeq,Matrix.det_smul,Fintype.card_fin,abs_mul,abs_pow]
  have hReduced : Real.exp (L*t z) *
      referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z =
      r^2 * |(operatorMatrixMap J).det| *
        (-coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) (X z)) := by
    apply mul_left_cancel₀ (abs_pos.mpr hr0).ne'
    rw [hScaled,hDet,← sq_abs r]
    ring
  have hExp : Real.exp (-L*t z) * Real.exp (L*t z) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  change referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z =
    (r^2 * |(operatorMatrixMap J).det| * Real.exp (-L*t z)) *
      (-coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) (X z))
  calc
    _ = Real.exp (-L*t z) * (Real.exp (L*t z) *
        referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z) := by
      rw [← mul_assoc,hExp,one_mul]
    _ = Real.exp (-L*t z) * (r^2 * |(operatorMatrixMap J).det| *
        (-coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1) (X z))) := by
      rw [hReduced]
    _ = _ := by ring

theorem referenceOrdinaryStrongDriftFamily_physical_harmonic_eq_zero
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0) (u : SmoothData)
    (hphysical : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) = 0) :
    referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
      (smoothBallSobolev (s+2)
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u)) = 0 := by
  apply (referenceOrdinaryStrongDriftFamily_smooth_eq_zero_iff
    g L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy r hr
      (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u)).mpr
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with z hz
  rw [referenceRescaledPositiveExpression_physical_pullback_eq
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hr0 u z hz,
    hphysical z hz,neg_zero,mul_zero,Pi.zero_apply]

theorem referenceHarmonicLiftFamily_physical_harmonic_eq_self
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0) (u : SmoothData)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).IsInvertible)
    (hphysical : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) = 0) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
      (smoothBallSobolev (s+2)
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u)) =
      smoothBallSobolev (s+2)
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u) := by
  rw [referenceHarmonicLiftFamily_eq_strongHarmonicProjection
    g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r) hi]
  apply strongHarmonicProjectionL_eq_self
  exact referenceOrdinaryStrongDriftFamily_physical_harmonic_eq_zero
    g hg L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy r hr hr0 u hphysical

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
