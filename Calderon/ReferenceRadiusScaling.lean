import Calderon.ReferenceProfileBounds

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

/-- The actual manuscript radius from the integrated reference depth. -/
def referenceRadius (δ R : ℝ) (p : ℕ) (L : ℝ) (x : R3) : ℝ :=
  R * (softplus δ (referenceDepth L x)) ^ p

lemma referenceRadius_pos (δ R : ℝ) (p : ℕ) (L : ℝ) (x : R3)
    (hδ : 0 < δ) (hR : 0 < R) : 0 < referenceRadius δ R p L x :=
  mul_pos hR (pow_pos (softplus_pos δ _ hδ) p)

lemma log_referenceRadius (δ R : ℝ) (p : ℕ) (L : ℝ) (hδ : 0 < δ) (hR : 0 < R) :
    (fun x => Real.log (referenceRadius δ R p L x)) =
      logProfile δ (Real.log R) p (referenceDepth L) := by
  funext x
  unfold referenceRadius logProfile
  rw [Real.log_mul (ne_of_gt hR) (pow_ne_zero p (ne_of_gt (softplus_pos δ _ hδ))),
    Real.log_pow]

lemma radius_gradient_power_scale_bound (δ t R C b : ℝ) (p j : ℕ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hb : 0 ≤ b) (hj : j ≤ p)
    (hbound : b ≤ (p : ℝ) * C * logSlope δ t) :
    (R * (softplus δ t) ^ p) * b ^ j ≤
      R * (p : ℝ) ^ j * C ^ j * (softplus δ t) ^ (p - j) := by
  have hs := softplus_pos δ t hδ
  have ha := logSlope_pos δ t hδ
  have hm : 0 ≤ logSlope δ t * softplus δ t := mul_nonneg ha.le hs.le
  have hm1 : logSlope δ t * softplus δ t ≤ 1 := by
    rw [logSlope_mul_softplus δ t hδ]
    exact (softplus_derivative_lt_one δ t).le
  have hpwr : (logSlope δ t * softplus δ t) ^ j ≤ 1 := pow_le_one₀ hm hm1
  have hpow : (softplus δ t) ^ p = (softplus δ t) ^ (p - j) * (softplus δ t) ^ j := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (R * (softplus δ t) ^ p) * b ^ j ≤
        (R * (softplus δ t) ^ p) * ((p : ℝ) * C * logSlope δ t) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hbound j) (by positivity)
    _ = (R * (p : ℝ) ^ j * C ^ j * (softplus δ t) ^ (p - j)) *
        (logSlope δ t * softplus δ t) ^ j := by
      rw [hpow]
      simp only [mul_pow]
      ring
    _ ≤ (R * (p : ℝ) ^ j * C ^ j * (softplus δ t) ^ (p - j)) * 1 :=
      mul_le_mul_of_nonneg_left hpwr (by positivity)
    _ = R * (p : ℝ) ^ j * C ^ j * (softplus δ t) ^ (p - j) := mul_one _

lemma radius_gradient_power_uniform_scale_bound (δ t T R C b : ℝ) (p j : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : t ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hb : 0 ≤ b) (hj : j ≤ p) (hbound : b ≤ (p : ℝ) * C * logSlope δ t) :
    (R * (softplus δ t) ^ p) * b ^ j ≤
      R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  have hbase := radius_gradient_power_scale_bound δ t R C b p j hδ hR hC hb hj hbound
  have hpow := pow_le_pow_left₀ (softplus_pos δ t hδ).le
    (softplus_le_log_exp_upper δ t T hδ hδ1 ht) (p - j)
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem exists_referenceRadius_metric_power_bounds_on_compact
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C T : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p j : ℕ, j ≤ p → ∀ x ∈ K,
      referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric g L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ j ≤
        R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_referenceDepth_metricNorm_bounds_on_compact g hg L hL K hK
  refine ⟨C, T, hC, ?_⟩
  intro δ hδ hδ1 R hR p j hj x hx
  rw [log_referenceRadius δ R p L hδ hR]
  obtain ⟨hmin, hmax, ht⟩ := hbounds x hx
  have hb : 0 ≤ metricDifferentialNorm (referenceMetric g L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x := Real.sqrt_nonneg _
  have hbound : metricDifferentialNorm (referenceMetric g L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x ≤
      (p : ℝ) * C * logSlope δ (referenceDepth L x) := by
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have h := mul_le_mul_of_nonneg_left hmax
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (referenceDepth L x) hδ).le)
    convert h using 1 <;> ring
  exact radius_gradient_power_uniform_scale_bound δ _ T R C _ p j hδ hδ1 ht hR.le hC.le hb hj hbound

lemma referenceRadius_zero_upper_bound (δ R : ℝ) (p : ℕ) (L : ℝ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hL : 0 < L) :
    referenceRadius δ R p L 0 ≤ R * (δ * Real.log 2) ^ p := by
  apply mul_le_mul_of_nonneg_left _ hR
  exact pow_le_pow_left₀ (softplus_pos δ _ hδ).le
    (softplus_le_delta_log_two δ _ hδ (referenceDepth_zero_neg L hL).le) p

end OAI.AnisotropicCalderon.ConformalDepth
