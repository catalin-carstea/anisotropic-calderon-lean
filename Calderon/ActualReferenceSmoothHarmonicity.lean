import Calderon.ActualReferenceZeroRadiusCoefficients
import Calderon.NativePrincipalSmoothFluxDictionary
import Calderon.SmoothPrincipalCompactTests
import Calderon.CoordinateGradientLaplacian
import Calderon.NativePolynomialAnalyticLaplacian
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap

theorem ordinaryPrincipalL_zero_smoothBallSobolev_of_flux_harmonic
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (u : SmoothData)
    (hHarm : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (coefficientMatrixField 2 F x) (gradient u.1 x)) z = 0) :
    ordinaryPrincipalL hcalc 0 F (smoothBallSobolev 2 u) = 0 := by
  have h := ordinaryPrincipalL_smoothBallSobolev_value_ae_coordinateFlux hcalc 0 F u
  rw [TauCeti.Wkp.value_zero] at h
  apply Lp.ext
  filter_upwards [h,ae_restrict_mem ballOpens.isOpen.measurableSet,
    Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with z hz hzB hzero
  rw [hz,hHarm z hzB,hzero]
  simp only [neg_zero,Pi.zero_apply]

theorem flux_harmonic_of_ordinaryPrincipalL_zero_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (u : SmoothData)
    (hP : ordinaryPrincipalL hcalc 0 F (smoothBallSobolev 2 u) = 0) :
    ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (coefficientMatrixField 2 F x) (gradient u.1 x)) z = 0 := by
  have h := ordinaryPrincipalL_smoothBallSobolev_value_ae_coordinateFlux hcalc 0 F u
  rw [TauCeti.Wkp.value_zero,hP] at h
  have hZero : (fun z => -coordinateFluxDivergence (fun x => matrixOperatorMap (coefficientMatrixField 2 F x) (gradient u.1 x)) z) =ᵐ[(volume : Measure R3).restrict ballOpens] (fun _ => (0 : ℝ)) := by
    filter_upwards [h,Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with z hz hzero
    rw [hzero] at hz
    exact hz.symm
  have hT := contDiff_neg_coordinateFluxDivergence_matrixGradient (coefficientMatrixField 2 F)
    (fun i j => contDiff_coefficientValue 2 (F i j)) u.1 u.2
  have hEq := Measure.eqOn_open_of_ae_eq hZero (show IsOpen (ballOpens : Set R3) from isOpen_ball)
    hT.continuous.continuousOn continuousOn_const
  intro z hz
  have he := hEq hz
  exact neg_eq_zero.mp he

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
theorem ordinaryPrincipalL_referencePhysicalGauge_smooth_eq_zero
    (hcalc : FixedSobolevCalculus) (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData)
    (hHarm : ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient u.1 x)) z = 0) :
    ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
      (smoothBallSobolev 2 u) = 0 := by
  apply ordinaryPrincipalL_zero_smoothBallSobolev_of_flux_harmonic
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  exact hHarm

include hg hData in
theorem coordinateFluxDivergence_referencePhysicalGauge_radius_zero
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (u : SmoothData) (z : R3) (hz : z ∈ (ballOpens : Set R3)) :
    coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),x)) (gradient u.1 x)) z =
      (referencePhysicalHalfGauge g L Φ ((q,(y,0)),0))^2 * GreenRadialTrace.euclideanLaplacian u.1 z := by
  let c0 : ℝ := (referencePhysicalHalfGauge g L Φ ((q,(y,0)),0))^2
  have hGerm : (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),x)) (gradient u.1 x)) =ᶠ[𝓝 z] (fun x => c0 • gradient u.1 x) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    rw [referencePhysicalGaugeCompactPrincipalCoefficient_radius_zero_on_unitBall g hg L y0 Φ B ε C ρ H a w hData q hq y hy x (ball_subset_closedBall hx),map_smul,ContinuousLinearMap.smul_apply]
    have hId : matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ) = ContinuousLinearMap.id ℝ R3 := by
      exact matrixOperatorAlgEquiv.map_one
    rw [hId,ContinuousLinearMap.id_apply]
  have hDiv : coordinateFluxDivergence (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),x)) (gradient u.1 x)) z = coordinateFluxDivergence (fun x => c0 • gradient u.1 x) z := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have he : (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),x)) (gradient u.1 x) i) =ᶠ[𝓝 z] (fun x => (c0 • gradient u.1 x) i) :=
      hGerm.mono (fun x hx => congrArg (fun v : R3 => v i) hx)
    rw [he.fderiv_eq (𝕜 := ℝ)]
  have hScalar : coordinateFluxDivergence (fun x => c0 • gradient u.1 x) z = c0 * coordinateFluxDivergence (gradient u.1) z := by
    unfold coordinateFluxDivergence
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hD : DifferentiableAt ℝ (fun x => gradient u.1 x i) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z ((contDiff_actual_scalarGradient u.1 u.2).differentiable (by simp) z)
    change fderiv ℝ (fun x => c0 * gradient u.1 x i) z (NormalCoordinatesFrame.coordinateVector i) = _
    rw [fderiv_const_mul hD c0]
    rfl
  rw [hDiv,hScalar,coordinateFluxDivergence_gradient_eq_laplacian_of_contDiff u.1 (u.2.of_le (by simp)),GreenRadialTrace.analyticLaplacian_eq_euclideanLaplacian u.1 u.2 z]

include hg hData in
theorem referencePhysicalGauge_radius_zero_harmonic_of_euclideanHarmonic
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (u : SmoothData) (hu : ∀ z ∈ (ballOpens : Set R3), GreenRadialTrace.euclideanLaplacian u.1 z = 0) :
    ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),x)) (gradient u.1 x)) z = 0 := by
  intro z hz
  rw [coordinateFluxDivergence_referencePhysicalGauge_radius_zero g hg L y0 Φ B ε C ρ H a w hData q hq y hy u z hz,hu z hz,mul_zero]

include hg hData in
theorem referencePhysicalGauge_flux_harmonic_of_ordinaryPrincipalL_zero
    (hcalc : FixedSobolevCalculus) (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData)
    (hP : ordinaryPrincipalL hcalc 0 (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
      (smoothBallSobolev 2 u) = 0) :
    ∀ z ∈ (ballOpens : Set R3), coordinateFluxDivergence
      (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient u.1 x)) z = 0 := by
  have h := flux_harmonic_of_ordinaryPrincipalL_zero_smoothBallSobolev hcalc
    (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) u hP
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets] at h
  exact h

end OAI.AnisotropicCalderon.ConnectionError
