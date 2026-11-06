import Calderon.ActualHalfGaugeCompactWeakPole
import Calderon.ActualHalfGaugeCollarForcingSupport
import Calderon.ParametrixFixedCutoffs
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise Distributions
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)

include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_ae_zero_off_halfBall
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens,
      z ∉ closedBall (0 : R3) (1/2) → TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z = 0 := by
  classical
  let η : R3 → ℝ := fun z => if z ∈ closedBall (0 : R3) (1/2) then 0 else 1
  have hη : ∀ z ∈ closedBall (0 : R3) (1/2), η z = 0 := by
    intro z hz
    simp only [η,ite_eq_left hz]
  have hF := referencePhysicalHalfGaugeCollarForcing_cutoff_ae_zero g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero
    (1/2) η hθOne hζOne hη q hq y hy r hr
  filter_upwards [hF] with z hz hza
  have hηz : η z = 1 := by simp only [η,ite_eq_right hza]
  rw [hηz,one_mul] at hz
  exact hz

include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_integrable_smooth_mul
    (q : ℝ) (y : R3) (r : ℝ) (u : SmoothData) :
    Integrable (fun z : R3 => TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * u.1 z)
      ((volume : Measure R3).restrict ballOpens) := by
  have hInt := MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) (TauCeti.Wkp.value 2 (smoothBallSobolev 2 u))
  apply hInt.congr
  filter_upwards [value_smoothBallSobolev_ae 2 u] with z hz
  rw [TauCeti.Wkp.value_zero]
  simp only [hz,Real.inner_apply]

include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_harmonic_value
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hHarm : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient u.1 x)) z = 0) :
    u.1 0 = -(∫ z : R3, TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * u.1 z
      ∂(volume : Measure R3).restrict ballOpens) := by
  let A : MatrixField := fun x => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)
  let V : R3 → ℝ := ((ballOpens : Set R3).indicator
    (fun z => normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r)) z - referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),z)))
  have hSupp : tsupport V ⊆ closedBall (0 : R3) (1/2) :=
    tsupport_zeroExtended_halfGaugeRemainder_subset (referencePhysicalHalfGauge g L Φ) θ ζ sphereSurfaceMass⁻¹ (q,(y,r)) (1/2) 1 hθOne hζOne
  have hProduct : (fun z : R3 => V z * (-coordinateFluxDivergence (fun x => matrixOperatorMap (A x) (gradient (parametrixHarmonicTest u) x)) z)) = 0 := by
    funext z
    change V z * (-coordinateFluxDivergence (fun x => matrixOperatorMap (A x) (gradient (parametrixHarmonicTest u) x)) z) = 0
    by_cases hz : V z = 0
    · rw [hz,zero_mul]
    have hza : z ∈ closedBall (0 : R3) (1/2) := hSupp (subset_closure hz)
    have hzBall : z ∈ (ballOpens : Set R3) := by
      apply mem_ball_zero_iff.mpr
      have hn := mem_closedBall_zero_iff.mp hza
      linarith
    rw [coordinateFluxDivergence_parametrixHarmonicTest_eq A u z hza,hHarm z hzBall,neg_zero,mul_zero]
  have hWeak := referencePhysicalHalfGaugeCompactWeakPole g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero q hq y hy r hr (parametrixHarmonicTest u)
  change (∫ z : R3, V z * (-coordinateFluxDivergence (fun x => matrixOperatorMap (A x) (gradient (parametrixHarmonicTest u) x)) z)) = _ at hWeak
  rw [hProduct] at hWeak
  have hI0 : integral (volume : Measure R3) (0 : R3 → ℝ) = 0 := by
    change (∫ _ : R3, (0 : ℝ)) = 0
    exact integral_zero _ _
  rw [hI0,parametrixHarmonicTest_zero] at hWeak
  have hF := referencePhysicalHalfGaugeCollarForcing_ae_zero_off_halfBall g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hθOne hζOne q hq y hy r hr
  have hIntEq : (∫ z : R3, TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * parametrixHarmonicTest u z ∂(volume : Measure R3).restrict ballOpens) =
      ∫ z : R3, TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * u.1 z ∂(volume : Measure R3).restrict ballOpens := by
    apply integral_congr_ae
    filter_upwards [hF] with z hz
    change TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * parametrixHarmonicTest u z = TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * u.1 z
    by_cases hza : z ∈ closedBall (0 : R3) (1/2)
    · rw [parametrixHarmonicTest_eq u z hza]
    · rw [hz hza,zero_mul,zero_mul]
  rw [hIntEq] at hWeak
  linarith

include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_harmonic_inner
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) (1/2), ζ z = 1)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (u : SmoothData)
    (hHarm : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient u.1 x)) z = 0) :
    u.1 0 = -⟪(referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))),TauCeti.Wkp.value 2 (smoothBallSobolev 2 u)⟫_ℝ := by
  have h := referencePhysicalHalfGaugeCollarForcing_harmonic_value g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero hθOne hζOne q hq y hy r hr u hHarm
  rw [MeasureTheory.L2.inner_def]
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards [value_smoothBallSobolev_ae 2 u] with z hz
  rw [TauCeti.Wkp.value_zero]
  simp only [hz,Real.inner_apply]

end OAI.AnisotropicCalderon.ConnectionError
