import Calderon.AngularEuclideanDensity
import Calderon.MetricOperator
import Calderon.MetricSmooth

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.AngularPolynomial

/-- Actual quadratic form of a variable real continuous linear operator. -/
def coefficientQuadratic (C : R3 → R3 →L[ℝ] R3) (x V : R3) : ℝ :=
  ⟪C x V, V⟫_ℝ

lemma compact_coefficient_quadratic_integrable (C : R3 → R3 →L[ℝ] R3)
    (rho : R3 → ℝ) (V : R3 → R3) (hC : Continuous C)
    (hr : Continuous rho) (hV : Continuous V) (hc : HasCompactSupport V) :
    Integrable (fun x => rho x * coefficientQuadratic C x (V x)) := by
  have hq : Continuous (fun x => rho x * coefficientQuadratic C x (V x)) :=
    hr.mul ((hC.clm_apply hV).inner hV)
  have hs : HasCompactSupport (fun x => rho x * coefficientQuadratic C x (V x)) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
    filter_upwards [hc] with x hx
    simp [coefficientQuadratic, hx]
  exact hq.integrable_of_hasCompactSupport hs

lemma coefficientQuadratic_add_smul (C : R3 → R3 →L[ℝ] R3)
    (hC : ∀ x V W, ⟪C x V, W⟫_ℝ = ⟪C x W, V⟫_ℝ)
    (x V A : R3) (t : ℝ) :
    coefficientQuadratic C x (V + t • A) = coefficientQuadratic C x V +
      t ^ 2 * coefficientQuadratic C x A + 2 * t * ⟪V, C x A⟫_ℝ := by
  unfold coefficientQuadratic
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial]
  rw [hC x V A, real_inner_comm (C x A) V]
  ring

theorem compact_coefficient_density_gradient_square_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (C : R3 → R3 →L[ℝ] R3)
    (hC : ContDiff ℝ ∞ C)
    (hsymm : ∀ x V W, ⟪C x V, W⟫_ℝ = ⟪C x W, V⟫_ℝ)
    (k : ℝ) (u rho : R3 → ℝ) (A : R3 → R3)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ rho) (hA : ContDiff ℝ ∞ A)
    (hc : HasCompactSupport u) :
    (∫ x : R3, rho x * coefficientQuadratic C x (gradient u x + (k * u x) • A x)) =
      (∫ x : R3, rho x * coefficientQuadratic C x (gradient u x)) +
        k ^ 2 * (∫ x : R3, rho x * coefficientQuadratic C x (A x) * u x ^ 2) -
          k * (∫ x : R3, densityWeightedDivergence b rho (fun y => C y (A y)) x * u x ^ 2) := by
  have hg : Continuous (gradient u) := (hu.gradient_right (m := 0) (by simp)).continuous
  have hCA : ContDiff ℝ ∞ (fun x => C x (A x)) := hC.clm_apply hA
  have hgrad := compact_coefficient_quadratic_integrable C rho (gradient u)
    hC.continuous hr.continuous hg (gradient_hasCompactSupport u hc)
  have hpot : Integrable (fun x : R3 => rho x * coefficientQuadratic C x (A x) * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable
      (fun x : R3 => rho x * coefficientQuadratic C x (A x)) u
      (hr.continuous.mul ((hC.continuous.clm_apply hA.continuous).inner hA.continuous))
      hu.continuous hc
  have hcross : Integrable (fun x : R3 => rho x * (2 * u x * ⟪gradient u x, C x (A x)⟫_ℝ)) := by
    convert compact_scalar_product_integrable rho u
      (fun x => 2 * ⟪gradient u x, C x (A x)⟫_ℝ) hr.continuous hu.continuous
      (continuous_const.mul (hg.inner hCA.continuous)) hc using 1
    funext x
    ring
  have hp : (fun x : R3 => rho x * coefficientQuadratic C x
      (gradient u x + (k * u x) • A x)) =
      fun x => (rho x * coefficientQuadratic C x (gradient u x) +
        k ^ 2 * (rho x * coefficientQuadratic C x (A x) * u x ^ 2)) +
        k * (rho x * (2 * u x * ⟪gradient u x, C x (A x)⟫_ℝ)) := by
    funext x
    rw [coefficientQuadratic_add_smul C hsymm]
    ring
  rw [hp, integral_add (f := fun x : R3 => rho x * coefficientQuadratic C x (gradient u x) +
      k ^ 2 * (rho x * coefficientQuadratic C x (A x) * u x ^ 2))
    (g := fun x : R3 => k * (rho x * (2 * u x * ⟪gradient u x, C x (A x)⟫_ℝ)))
    (hgrad.add (hpot.const_mul (k ^ 2))) (hcross.const_mul k),
    integral_add hgrad (hpot.const_mul (k ^ 2)), integral_const_mul, integral_const_mul,
    compact_density_gradient_cross_term b u rho (fun y => C y (A y)) hu hr hCA hc]
  ring

theorem compact_coefficient_density_gradient_profile_lower_bound {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (C : R3 → R3 →L[ℝ] R3)
    (hC : ContDiff ℝ ∞ C)
    (hsymm : ∀ x V W, ⟪C x V, W⟫_ℝ = ⟪C x W, V⟫_ℝ)
    (k c : ℝ) (hk : 0 ≤ k) (u rho beta : R3 → ℝ) (A : R3 → R3)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ rho) (hb : Continuous beta)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport u)
    (hdiv : ∀ x, u x ≠ 0 → densityWeightedDivergence b rho (fun y => C y (A y)) x ≤
      -c * (rho x * beta x)) :
    (∫ x : R3, rho x * coefficientQuadratic C x (gradient u x)) +
      k ^ 2 * (∫ x : R3, rho x * coefficientQuadratic C x (A x) * u x ^ 2) +
      k * c * (∫ x : R3, (rho x * beta x) * u x ^ 2) ≤
    (∫ x : R3, rho x * coefficientQuadratic C x (gradient u x + (k * u x) • A x)) := by
  have hCA : ContDiff ℝ ∞ (fun x => C x (A x)) := hC.clm_apply hA
  have hd : Integrable (fun x : R3 => densityWeightedDivergence b rho
      (fun y => C y (A y)) x * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable _ u
      (densityWeightedDivergence_continuous b rho _ hr hCA) hu.continuous hc
  have hm : Integrable (fun x : R3 => (rho x * beta x) * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable (fun x : R3 => rho x * beta x) u
      (hr.continuous.mul hb) hu.continuous hc
  have hi : (∫ x : R3, densityWeightedDivergence b rho (fun y => C y (A y)) x * u x ^ 2) ≤
      -c * (∫ x : R3, (rho x * beta x) * u x ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono hd (hm.const_mul (-c))
    intro x
    by_cases hx : u x = 0
    · simp [hx]
    · have h := mul_le_mul_of_nonneg_right (hdiv x hx) (sq_nonneg (u x))
      convert h using 1 <;> ring
  rw [compact_coefficient_density_gradient_square_expansion b C hC hsymm k u rho A hu hr hA hc]
  nlinarith [mul_le_mul_of_nonneg_left hi hk]

/-- The actual inverse endomorphism of the frozen metric. -/
def inverseMetricOperator (g : MatrixField) : R3 → R3 →L[ℝ] R3 :=
  ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g)

lemma contDiff_inverseMetricOperator (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ (inverseMetricOperator g) :=
  ConnectionError.contDiff_inverseMetricField _ (MetricOperator.contDiff_metricOperatorField g hg)
    (MetricOperator.isUnit_metricOperatorField g hg)

lemma inverseMetricOperator_symmetric (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x V W : R3) : ⟪inverseMetricOperator g x V, W⟫_ℝ =
      ⟪inverseMetricOperator g x W, V⟫_ℝ := by
  have h := MetricOperator.metricOperatorField_symmetric g hg x
    (inverseMetricOperator g x V) (inverseMetricOperator g x W)
  change ⟪MetricOperator.metricOperatorField g x
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) x V),
    inverseMetricOperator g x W⟫_ℝ =
    ⟪MetricOperator.metricOperatorField g x
      (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) x W),
      inverseMetricOperator g x V⟫_ℝ at h
  rw [ConnectionError.metric_apply_inverseMetricField _
    (MetricOperator.isUnit_metricOperatorField g hg),
    ConnectionError.metric_apply_inverseMetricField _
      (MetricOperator.isUnit_metricOperatorField g hg)] at h
  simpa only [real_inner_comm] using h.symm

lemma inverseMetricOperator_eq_matrix_inverse (g : MatrixField) (hg : IsAdmissibleMetric g)
    (x : R3) : inverseMetricOperator g x = MetricOperator.matrixOperatorMap ((g x)⁻¹) :=
  MetricOperator.inverseMetricField_eq_matrix_inverse g hg x

lemma coefficientQuadratic_inverseMetricOperator (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x V : R3) :
    coefficientQuadratic (inverseMetricOperator g) x V =
      TauCeti.PDE.matrixBilinearForm ((g x)⁻¹) V V := by
  unfold coefficientQuadratic
  rw [inverseMetricOperator_eq_matrix_inverse g hg]
  change ⟪(g x)⁻¹.toEuclideanLin V, V⟫_ℝ = _
  rw [TauCeti.PDE.matrixBilinearForm_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rfl

lemma coefficientQuadratic_inverseMetricOperator_nonneg (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x V : R3) :
    0 ≤ coefficientQuadratic (inverseMetricOperator g) x V := by
  rw [coefficientQuadratic_inverseMetricOperator g hg, TauCeti.PDE.matrixBilinearForm_apply]
  exact (hg.posDef x).inv.posSemidef.dotProduct_mulVec_nonneg (V : Fin 3 → ℝ)

lemma vol_coefficientQuadratic_inverseMetricOperator_nonneg (g : MatrixField)
    (hg : IsAdmissibleMetric g) (x V : R3) :
    0 ≤ vol g x * coefficientQuadratic (inverseMetricOperator g) x V :=
  mul_nonneg (EnergyBridge.vol_pos g hg x).le
    (coefficientQuadratic_inverseMetricOperator_nonneg g hg x V)

lemma vol_coefficientQuadratic_eq_energyIntegrand (g : MatrixField)
    (hg : IsAdmissibleMetric g) (u : R3 → ℝ) (x : R3) :
    vol g x * coefficientQuadratic (inverseMetricOperator g) x (gradient u x) =
      TauCeti.PDE.energyIntegrand (EnergyBridge.principalCoefficient g x) 0 0
        (EnergyBridge.energyJet u x) (EnergyBridge.energyJet u x) := by
  rw [coefficientQuadratic_inverseMetricOperator g hg]
  simp only [TauCeti.PDE.energyIntegrand_apply, EnergyBridge.energyJet,
    EnergyBridge.energyGradient_eq_gradient, TauCeti.PDE.driftForm_apply,
    TauCeti.PDE.massForm_apply, inner_zero_left, zero_mul, add_zero]
  exact (TauCeti.PDE.matrixBilinearForm_smul_apply (vol g x) ((g x)⁻¹)
    (gradient u x) (gradient u x)).symm

theorem compact_metric_density_gradient_square_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (k : ℝ) (u f : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport u) :
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
      (gradient u x + (k * u x) • gradient f x)) =
      (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x (gradient u x)) +
        k ^ 2 * (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
          (gradient f x) * u x ^ 2) -
        k * (∫ x : R3, densityWeightedDivergence b (vol g)
          (fun y => inverseMetricOperator g y (gradient f y)) x * u x ^ 2) :=
  compact_coefficient_density_gradient_square_expansion b _
    (contDiff_inverseMetricOperator g hg) (inverseMetricOperator_symmetric g hg)
    k u (vol g) (gradient f) hu (EnergyBridge.contDiff_vol g hg)
    (hf.gradient_right (m := ∞) (by simp)) hc

theorem compact_metric_density_gradient_profile_lower_bound {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (k c : ℝ) (hk : 0 ≤ k) (u f beta : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hb : Continuous beta)
    (hc : HasCompactSupport u)
    (hdiv : ∀ x, u x ≠ 0 → densityWeightedDivergence b (vol g)
      (fun y => inverseMetricOperator g y (gradient f y)) x ≤ -c * (vol g x * beta x)) :
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x (gradient u x)) +
      k ^ 2 * (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
        (gradient f x) * u x ^ 2) + k * c * (∫ x : R3, (vol g x * beta x) * u x ^ 2) ≤
    (∫ x : R3, vol g x * coefficientQuadratic (inverseMetricOperator g) x
      (gradient u x + (k * u x) • gradient f x)) :=
  compact_coefficient_density_gradient_profile_lower_bound b _
    (contDiff_inverseMetricOperator g hg) (inverseMetricOperator_symmetric g hg)
    k c hk u (vol g) beta (gradient f) hu (EnergyBridge.contDiff_vol g hg) hb
    (hf.gradient_right (m := ∞) (by simp)) hc hdiv

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_coefficient_density_gradient_square_expansion
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_coefficient_density_gradient_profile_lower_bound
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.inverseMetricOperator_symmetric
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_metric_density_gradient_square_expansion
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_metric_density_gradient_profile_lower_bound
