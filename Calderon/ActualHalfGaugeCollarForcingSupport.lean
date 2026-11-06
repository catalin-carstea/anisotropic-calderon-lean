import Calderon.ActualHalfGaugeCollarForcing
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
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
theorem referencePhysicalHalfGaugeCollarForcing_value_ae_principal
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => (-coordinateFluxDivergence
        (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
          (gradient (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r))) x)) z) -
        (-coordinateFluxDivergence
          (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
            (gradient (fun v => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),v)) x)) z)) := by
  have hOne : ∀ z ∈ ball (0 : R3) 1, coefficientSpatialBump z = 1 := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
    exact coefficientSpatialBump_eq_one z hn.le
  have hQ : (referencePhysicalHalfGaugeResidualZero g hg L y0 Φ B ε C ρ H a w hData (q,(y,r)) : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => -coordinateFluxDivergence (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x))
        (gradient (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r))) x)) z) := by
    exact actualReferenceHalfGaugedResidualLpFamily_ae_divergence g hg L y0 Φ B ε C ρ H a w hData
      coefficientSpatialBump coefficientSpatialBump.contDiff coefficientSpatialBump.hasCompactSupport
      sphereSurfaceMass⁻¹ 1 hOne q hq y hy r hr
  have hF := referencePhysicalHalfGaugeCollarForcing_value_ae g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))
  have hProfile := referencePhysicalHalfGaugeResidualZero_ae_profile g hg L y0 Φ B ε C ρ H a w hData (q,(y,r))
  rw [TauCeti.Wkp.value_zero] at hF hProfile ⊢
  filter_upwards [hF,hProfile,hQ] with z hF hPr hQ
  rw [hF,← hPr,hQ]
include hg hData hcalc in
theorem referencePhysicalHalfGaugeCollarForcing_cutoff_ae_zero
    (a0 : ℝ) (η : R3 → ℝ)
    (hθOne : ∀ z ∈ ball (0 : R3) 1, θ z = 1)
    (hζOne : ∀ z ∉ closedBall (0 : R3) a0, ζ z = 1)
    (hηZero : ∀ z ∈ closedBall (0 : R3) a0, η z = 0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    ∀ᵐ z ∂(volume : Measure R3).restrict ballOpens,
      η z * TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z = 0 := by
  have hF := referencePhysicalHalfGaugeCollarForcing_value_ae_principal g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero
    q hq y hy r hr
  rw [TauCeti.Wkp.value_zero] at hF ⊢
  filter_upwards [hF,ae_restrict_mem ballOpens.isOpen.measurableSet] with z hF hz
  by_cases hηz : η z = 0
  · rw [hηz,zero_mul]
  have hzA : z ∉ closedBall (0 : R3) a0 := fun h => hηz (hηZero z h)
  have hzBall : z ∈ ball (0 : R3) 1 := hz
  have hNear : (fun v => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),v)) =ᶠ[𝓝 z] (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r))) := by
    filter_upwards [isOpen_ball.mem_nhds hzBall,
      isClosed_closedBall.isOpen_compl.mem_nhds hzA] with x hx hxA
    exact halfGaugeCollarField_eq_normalizedPotential (referencePhysicalHalfGauge g L Φ) θ ζ sphereSurfaceMass⁻¹ (q,(y,r)) x
      (hθOne x hx) (hζOne x hxA)
  have hDiv := coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq
    (fun x => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (fun v => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),v)) (normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r))) z hNear
  rw [hF,hDiv,sub_self,mul_zero]
end OAI.AnisotropicCalderon.ConnectionError
