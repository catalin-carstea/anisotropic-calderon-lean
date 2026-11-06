import Calderon.ActualHalfGaugeCollarForcing
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise Distributions
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap NativePolynomialBulkMoments

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def normalizedHalfGaugeResidualProfile
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (s : P × R3 → ℝ) (c0 : ℝ) (x : P × R3) : ℝ :=
  halfGaugeResidualRatio s x * normalCoefficientResidualProfile a c0 x +
    (inverseNormPotential c0 x.2 / s (x.1,0)) * scalarCoefficientPotential a s x

theorem integrable_normalizedHalfGaugeResidualProfile_mul_compact
    (a : P × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (c0 : ℝ) (p : P)
    (φ : R3 → ℝ) (hφ : Continuous φ) (hCompact : HasCompactSupport φ) :
    Integrable (fun z : R3 => normalizedHalfGaugeResidualProfile a s c0 (p,z) * φ z) := by
  have hS : Continuous (fun z : R3 => s (p,z)) := (hs.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hV : Continuous (fun z : R3 => scalarCoefficientPotential a s (p,z)) :=
    ((contDiff_scalarCoefficientPotential a s ha hs).comp (contDiff_const.prodMk contDiff_id)).continuous
  have hI1 := integrable_normalCoefficientResidualProfile_mul_compact a ha c0 p
    (fun z => (s (p,z) / s (p,0)) * φ z) ((hS.div_const _).mul hφ) hCompact.mul_left
  have hI2 := integrable_inverseNormPotential_mul_continuous_compact c0
    (fun z => (scalarCoefficientPotential a s (p,z) / s (p,0)) * φ z)
    ((hV.div_const _).mul hφ) hCompact.mul_left
  apply (hI1.add hI2).congr
  exact Filter.Eventually.of_forall fun z => by
    dsimp only [Pi.add_apply,normalizedHalfGaugeResidualProfile,halfGaugeResidualRatio]
    ring
variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0)

include hg hData hcalc in
theorem referencePhysicalHalfGaugeCompactWeakPole
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (φ : 𝓓(ballOpens, ℝ)) :
    (∫ z : R3, ((ballOpens : Set R3).indicator
      (fun v => normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r)) v - referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),v))) z *
      (-coordinateFluxDivergence (fun x => matrixOperatorMap (referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)) (gradient (φ : R3 → ℝ) x)) z)) =
      φ 0 + ∫ z : R3, TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * φ z ∂(volume : Measure R3).restrict ballOpens := by
  let A : MatrixField := fun x => referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x)
  let Q : R3 → ℝ := normalizedHalfGaugePotential (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ (q,(y,r))
  let W : R3 → ℝ := fun x => referencePhysicalHalfGaugeCollarField g L Φ θ ζ sphereSurfaceMass⁻¹ ((q,(y,r)),x)
  let T : R3 → ℝ := fun x => -coordinateFluxDivergence (fun z => matrixOperatorMap (A z) (gradient (φ : R3 → ℝ) z)) x
  let PW : R3 → ℝ := fun x => -coordinateFluxDivergence (fun z => matrixOperatorMap (A z) (gradient W z)) x
  let Rq : R3 → ℝ := fun x => normalizedHalfGaugeResidualProfile a (referencePhysicalHalfGauge g L Φ) sphereSurfaceMass⁻¹ ((q,(y,r)),x)
  have hASmooth : ContDiff ℝ ∞ A :=
    (contDiff_referencePhysicalGaugeCompactPrincipalCoefficient g hg L y0 Φ B ε C ρ H a w hData).comp (contDiff_const.prodMk contDiff_id)
  have hAEntry (i j : Fin 3) : ContDiff ℝ ∞ (fun z => A z i j) :=
    contDiff_pi.mp (contDiff_pi.mp hASmooth i) j
  have hW : ContDiff ℝ ∞ W :=
    (contDiff_referencePhysicalHalfGaugeCollarField g hg L y0 Φ B ε C ρ H a w hData θ ζ hθ hζ hCompact b hb hZero sphereSurfaceMass⁻¹).comp
      (contDiff_const.prodMk contDiff_id)
  have hSym (x : R3) (i j : Fin 3) : A x i j = A x j i := by
    have hEq := referencePhysicalHalfGauge_sq_smul_native g L y0 Φ B ε C ρ H a w hData ((q,(y,r)),x)
    change referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x) i j = referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,r)),x) j i
    rw [← hEq]
    change (referencePhysicalHalfGauge g L Φ ((q,(y,r)),x))^2 * a ((q,(y,r)),x) i j = (referencePhysicalHalfGauge g L Φ ((q,(y,r)),x))^2 * a ((q,(y,r)),x) j i
    rw [(referenceNativePrincipalCoefficient_isSymm g L y0 Φ B ε C ρ H a w hData ((q,(y,r)),x)).apply j i]
  have hT : ContDiff ℝ ∞ T := contDiff_neg_coordinateFluxDivergence_matrixGradient A hAEntry φ φ.contDiff
  have hTc : HasCompactSupport T := hasCompactSupport_neg_coordinateFluxDivergence_matrixGradient A φ φ.hasCompactSupport
  have hPW : ContDiff ℝ ∞ PW := contDiff_neg_coordinateFluxDivergence_matrixGradient A hAEntry W hW
  have hS : ContDiff ℝ ∞ (fun z : R3 => referencePhysicalHalfGauge g L Φ ((q,(y,r)),z)) :=
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData).comp (contDiff_const.prodMk contDiff_id)
  have hWeight : Continuous (fun z => T z / (referencePhysicalHalfGauge g L Φ ((q,(y,r)),0) * referencePhysicalHalfGauge g L Φ ((q,(y,r)),z))) :=
    hT.continuous.div (continuous_const.mul hS.continuous)
      (fun z => mul_ne_zero (referencePhysicalHalfGauge_pos g L Φ ((q,(y,r)),0)).ne'
        (referencePhysicalHalfGauge_pos g L Φ ((q,(y,r)),z)).ne')
  have hWeightSupport : HasCompactSupport (fun z => T z / (referencePhysicalHalfGauge g L Φ ((q,(y,r)),0) * referencePhysicalHalfGauge g L Φ ((q,(y,r)),z))) := by
    simpa only [div_eq_mul_inv] using
      (show HasCompactSupport (fun z => T z * (referencePhysicalHalfGauge g L Φ ((q,(y,r)),0) * referencePhysicalHalfGauge g L Φ ((q,(y,r)),z))⁻¹) from hTc.mul_right)
  have hIntQ : Integrable (fun z : R3 => Q z * T z) := by
    apply (integrable_inverseNormPotential_mul_continuous_compact sphereSurfaceMass⁻¹ _ hWeight hWeightSupport).congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [Q,normalizedHalfGaugePotential];ring
  have hIntW : Integrable (fun z : R3 => W z * T z) :=
    (hW.continuous.mul hT.continuous).integrable_of_hasCompactSupport hTc.mul_left
  have hIntRq : Integrable (fun z : R3 => Rq z * φ z) :=
    integrable_normalizedHalfGaugeResidualProfile_mul_compact a hData.1.2.2.2.2.2.2.2.2.1
      (referencePhysicalHalfGauge g L Φ) (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData) sphereSurfaceMass⁻¹ (q,(y,r))
      φ φ.continuous φ.hasCompactSupport
  have hIntPW : Integrable (fun z : R3 => φ z * PW z) :=
    (φ.continuous.mul hPW.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hWeakQ : (∫ z : R3, Q z * T z) = φ 0 + ∫ z : R3, Rq z * φ z :=
    integral_referenceNormalizedHalfGaugePotential_principal g hg L y0 Φ B ε C ρ H a w hData
      q hq y hy r hr φ φ.contDiff φ.hasCompactSupport
  have hWeakW : (∫ z : R3, W z * T z) = ∫ z : R3, φ z * PW z :=
    integral_smooth_mul_neg_matrixGradient_divergence_symm A hAEntry hSym W φ hW φ.contDiff φ.hasCompactSupport
  have hSubtract : (∫ z : R3, (Q z - W z) * T z) =
      φ 0 + ∫ z : R3, (Rq z - PW z) * φ z := by
    have hL : (fun z : R3 => (Q z-W z)*T z) = (fun z => Q z*T z-W z*T z) := by funext z;ring
    have hR : (fun z : R3 => (Rq z-PW z)*φ z) = (fun z => Rq z*φ z-φ z*PW z) := by funext z;ring
    rw [hL,hR,integral_sub hIntQ hIntW,integral_sub hIntRq hIntPW,hWeakQ,hWeakW]
    ring
  have hTSupp : tsupport T ⊆ (ballOpens : Set R3) :=
    (tsupport_neg_coordinateFluxDivergence_matrixGradient_subset A φ).trans φ.tsupport_subset
  have hTZero (z : R3) (hz : z ∉ (ballOpens : Set R3)) : T z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hTSupp h))
  have hLeft : (∫ z : R3, ((ballOpens : Set R3).indicator (fun v => Q v-W v)) z*T z) =
      ∫ z : R3, (Q z-W z)*T z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      change ((ballOpens : Set R3).indicator (fun v => Q v-W v)) z*T z = (Q z-W z)*T z
      by_cases hz : z ∈ (ballOpens : Set R3)
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz,hTZero z hz,zero_mul,mul_zero]
  have hForcing := referencePhysicalHalfGaugeCollarForcing_value_ae g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))
  have hRight : (∫ z : R3, TauCeti.Wkp.value 0 (referencePhysicalHalfGaugeCollarForcing g hg L y0 Φ B ε C ρ H a w hData hcalc θ ζ hθ hζ hCompact b hb hZero (q,(y,r))) z * φ z ∂(volume : Measure R3).restrict ballOpens) =
      ∫ z : R3, (Rq z-PW z)*φ z := by
    calc
      _ = ∫ z : R3, (Rq z-PW z)*φ z ∂(volume : Measure R3).restrict ballOpens := by
        apply integral_congr_ae
        filter_upwards [hForcing] with z hz
        rw [hz]
        rfl
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        simp only [φ.zero_on_compl hz,Pi.zero_apply,mul_zero])
  change (∫ z : R3, ((ballOpens : Set R3).indicator (fun v => Q v-W v)) z*T z) = _
  rw [hLeft,hRight,hSubtract]
end OAI.AnisotropicCalderon.ConnectionError
