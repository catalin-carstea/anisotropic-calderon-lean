import TaskInterface
import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.ActualReferencePhysicalOrientation
import Calderon.ActualPhysicalHarmonicCovariance
import Calderon.NativeSmoothOperatorRealization

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

theorem referencePhysicalGaugePrincipal_physical_harmonic_eq_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r) (u : SmoothData)
    (hphysical : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) = 0) :
    ordinaryPrincipalL hcalc 0
      (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
      (smoothBallSobolev 2
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u)) = 0
 := by
  let v : SmoothData := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u
  let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))
  have hp := hData.1
  rcases hp with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  have hBall2 (z : R3) (hz : z ∈ (ballOpens : Set R3)) : z ∈ closedBall (0 : R3) 2 := by
    change dist z (0 : R3) < 1 at hz
    change dist z (0 : R3) ≤ 2
    linarith
  have hBall1 (z : R3) (hz : z ∈ (ballOpens : Set R3)) : ‖z‖ ≤ 1 := by
    change dist z (0 : R3) < 1 at hz
    rw [dist_zero_right] at hz
    exact hz.le
  -- Physical covariance: the rescaled positive expression of the pullback vanishes.
  have hPhys (z : R3) (hz : z ∈ (ballOpens : Set R3)) :
      referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) v.1 z = 0 := by
    have h := referenceRescaledPositiveExpression_physical_pullback_eq
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos.ne' u z hz
    rw [hphysical z hz, neg_zero, mul_zero] at h
    exact h
  -- Conformal gauge: the weighted divergence form vanishes as well.
  have hConf (z : R3) (hz : z ∈ (ballOpens : Set R3)) :
      referenceRescaledConformalPositiveExpression g L Φ H (q,(y,r)) v.1 z = 0 := by
    rw [referenceRescaledConformalPositiveExpression_eq g L Φ H w hg y0 B ε C ρ a hData
      q hq y hy r hr z (hBall2 z hz) v.1 v.2, hPhys z hz, mul_zero]
  -- On the unit ball the exact F2 entries are the conformal principal coefficients.
  have hPrincipal (z : R3) (hz : z ∈ (ballOpens : Set R3)) (i j : Fin 3) :
      coefficientValue 2 (F i j) z =
        principalCoefficient (conformalMatrix (fun x => H ((q,(y,r)),x))
          (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) z i j := by
    have hc : coefficientValue 2 (F i j) z =
        referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),z) i j :=
      congrFun (coefficientValue_referencePhysicalGaugeCoefficientJets
        g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)) i j) z
    rw [hc, referencePhysicalGaugeCompactPrincipalCoefficient_eq_on_unitBall g L Φ H
      (q,(y,r)) z (hBall1 z hz), principalCoefficient_conformalMatrix _ _
      (fun x => hPos ((q,(y,r)),x)) z]
    all_goals first
      | rfl
      | simp only [principalCoefficient,vol,matrixPrincipalCoefficient,matrixVolumeDensity]
  have hTerm (x : R3) (i j : Fin 3) :
      DifferentiableAt ℝ
        (fun z => coefficientValue 2 (F i j) z * fderiv ℝ v.1 z (coordinateVector j)) x :=
    ((contDiff_coefficientValue 2 (F i j)).mul
      (smoothCoordinateDerivative v j).2).differentiable (by simp) x
  have hDiv (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      coordinateFluxDivergence (metricDivergenceFlux (conformalMatrix
        (fun x => H ((q,(y,r)),x)) (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) v.1) x =
        ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun z => coefficientValue 2 (F i j) z * fderiv ℝ v.1 z (coordinateVector j)) x
            (coordinateVector i) := by
    unfold coordinateFluxDivergence
    apply Finset.sum_congr rfl
    intro i _
    have hEq : (fun z => ∑ j : Fin 3,
        coefficientValue 2 (F i j) z * fderiv ℝ v.1 z (coordinateVector j)) =ᶠ[nhds x]
        (fun z => metricDivergenceFlux (conformalMatrix (fun x => H ((q,(y,r)),x))
          (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) v.1 z i) := by
      filter_upwards [ballOpens.isOpen.mem_nhds hx] with z hz
      rw [metricDivergenceFlux,matrixOperator_coordinate]
      simp_rw [gradient_coordinate]
      apply Finset.sum_congr rfl
      intro j _
      rw [hPrincipal z hz i j]
    rw [← hEq.fderiv_eq]
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => coefficientValue 2 (F i j) z * fderiv ℝ v.1 z (coordinateVector j))
      (fun j _ => hTerm x i j)]
    simp only [ContinuousLinearMap.sum_apply]
    try rfl
  have hValue := ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc 0 F v
  change TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F (smoothBallSobolev 2 v))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      (fun x => -∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun z => coefficientValue 2 (F i j) z *
          fderiv ℝ v.1 z (coordinateVector j)) x (coordinateVector i)) at hValue
  have hScalar : (fun x => -∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun z => coefficientValue 2 (F i j) z *
          fderiv ℝ v.1 z (coordinateVector j)) x (coordinateVector i))
      =ᵐ[((volume : Measure R3).restrict ballOpens)] (0 : R3 → ℝ) := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
    change _ = (0 : ℝ)
    rw [← hDiv x hx]
    exact hConf x hx
  apply TauCeti.Wkp.ext 0
  have hzero : TauCeti.Wkp.value 0 (0 : BallSobolev 0) = 0 :=
    map_zero (TauCeti.Wkp.valueL 0)
  rw [hzero]
  apply Lp.ext
  exact (hValue.trans hScalar).trans
    (Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)).symm

end OAI.AnisotropicCalderon.ConnectionError
