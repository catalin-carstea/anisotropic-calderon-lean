import Calderon.CommonProfileFamily
import Calderon.ActualDilatedDepthCofinalHessian
import Calderon.ReferenceWeightedApproximation

/-! Cofinal reference profile bounds and the degree/radius profile allocation for the
actual reference radius. The cofinal depth Hessian bound is Root's
`exists_dilated_referenceDepth_strict_hessian_bound_forall_ge`; it is only used here.
No coercivity claim. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile ReferenceWeightedApproximation

/-- The metric bounds of `exists_dilated_referenceRadius_uniform_metric_bounds` at an arbitrary
conformal parameter carrying the strict depth Hessian bound. -/
theorem exists_dilated_referenceRadius_metric_bounds_of_depth_hessian
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L)
    (hdepth : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField
          (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
        -⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) :
    ∃ c0 c1 C T : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p j : ℕ, j ≤ p → ∀ x ∈ K,
        c0 * (p : ℝ) ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y)) x ∧
        (∀ X : R3, coordinateHessian (fun y => Real.log (referenceRadius δ R p L y))
          (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
            (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
          -c1 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x *
              ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ j ≤
          R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  let a : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha : 0 < a := by
    dsimp [a]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  refine ⟨a * m, 1 / C, C, T, mul_pos ha hm, one_div_pos.mpr hC, hC, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p j hj x hx
  rw [log_referenceRadius δ R p L hδ hR]
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have hb : 0 ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x := Real.sqrt_nonneg _
  have hbound : metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
      (logProfile δ (Real.log R) p (referenceDepth L)) x ≤
      (p : ℝ) * C * logSlope δ (referenceDepth L x) := by
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have h := mul_le_mul_of_nonneg_left hmax
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (referenceDepth L x) hδ).le)
    convert h using 1 <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    have hs : a ≤ logSlope δ (referenceDepth L x) := logSlope_uniform_lower_bound δ _ T hδ hδ1 ht
    have h1 := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg p)
    have h2 := mul_le_mul h1 hmin hm.le
      (mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ _ hδ).le)
    convert h2 using 1 <;> ring
  · intro X
    exact coordinateHessian_logProfile_metric_le _
      (fun y => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg lam) y)
      δ (Real.log R) C p _ (contDiff_referenceDepth L) x X hδ hC hmax (hdepth lam hlam x hx X)
  · exact radius_gradient_power_uniform_scale_bound δ _ T R C _ p j hδ hδ1 ht hR.le hC.le hb hj hbound

/-- The original `referenceProfileBounds` Prop at an arbitrary conformal parameter carrying the
strict depth Hessian bound. -/
theorem exists_referenceProfileBounds_of_depth_hessian
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L)
    (hdepth : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ X : R3,
      coordinateHessian (referenceDepth L)
        (fun V W => coordinateConnectionField
          (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
          (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
        -⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) :
    ∃ c0 c1 J1 J2 D : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < J1 ∧ 0 < J2 ∧ 0 < D ∧
      referenceProfileBounds g K L c0 c1 J1 J2 D := by
  obtain ⟨c0, c1, _C, _T, hc0, hc1, -, hbounds⟩ :=
    exists_dilated_referenceRadius_metric_bounds_of_depth_hessian g hg K hK L hL hdepth
  obtain ⟨J1, J2, hJ1, hJ2, hjets⟩ :=
    exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at g hg K hK L hL
  obtain ⟨D, hD, hbeta⟩ :=
    exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at g hg K hK L hL
  refine ⟨c0, c1, J1, J2, D, hc0, hc1, hJ1, hJ2, hD, ?_⟩
  dsimp [referenceProfileBounds, referenceLogRadius, referenceProfileNorm]
  constructor
  · intro lam hlam δ hδ hδ1 R hR p hp x hx
    obtain ⟨hb, hH, hr⟩ := hbounds lam hlam δ hδ hδ1 R hR p 0 (Nat.zero_le p) x hx
    obtain ⟨hj1, hj2⟩ := hjets lam hlam δ hδ hδ1 R hR p hp x hx
    obtain ⟨hb1, hb2⟩ := hbeta lam hlam δ hδ hδ1 R hR p hp x hx
    refine ⟨hb, hH, ?_, hj1, hj2, hb1, hb2⟩
    exact densityWeightedDivergence_le_of_profile_hessian _
      (dilatedReferenceMetric_smooth_entries g hg lam L)
      (dilatedReferenceMetric_posDef g hg lam L) _
      (contDiff_log_referenceRadius δ R p L hδ hR) c1 x hH
  · intro p hp ε hε
    exact exists_dilated_referenceRadius_uniform_small_amplitude_at g hg K hK L hL p hp ε hε

/-- Cofinal metric bounds: one threshold, then every larger conformal parameter. -/
theorem exists_dilated_referenceRadius_metric_bounds_forall_ge
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ c0 c1 C T : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < C ∧
        ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
        ∀ p j : ℕ, j ≤ p → ∀ x ∈ K,
          c0 * (p : ℝ) ≤ metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ∧
          (∀ X : R3, coordinateHessian (fun y => Real.log (referenceRadius δ R p L y))
            (fun V W => coordinateConnectionField (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
              (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x V W) x X X ≤
            -c1 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
              (fun y => Real.log (referenceRadius δ R p L y)) x *
                ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X, X⟫_ℝ) ∧
          referenceRadius δ R p L x *
            metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
              (fun y => Real.log (referenceRadius δ R p L y)) x ^ j ≤
            R * (p : ℝ) ^ j * C ^ j * (Real.log (1 + Real.exp T)) ^ (p - j) := by
  obtain ⟨L0, hL0, hdepth⟩ := exists_dilated_referenceDepth_strict_hessian_bound_forall_ge g hg K hK
  exact ⟨L0, hL0, fun L hL => exists_dilated_referenceRadius_metric_bounds_of_depth_hessian
    g hg K hK L (hL0.trans_le hL) (hdepth L hL)⟩

/-- Cofinal `referenceProfileBounds`: one threshold, then the SAME Prop for every larger
conformal parameter, with positive constants depending on that parameter. -/
theorem exists_referenceProfileBounds_forall_ge
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∃ c0 c1 J1 J2 D : ℝ, 0 < c0 ∧ 0 < c1 ∧ 0 < J1 ∧ 0 < J2 ∧ 0 < D ∧
        referenceProfileBounds g K L c0 c1 J1 J2 D := by
  obtain ⟨L0, hL0, hdepth⟩ := exists_dilated_referenceDepth_strict_hessian_bound_forall_ge g hg K hK
  exact ⟨L0, hL0, fun L hL => exists_referenceProfileBounds_of_depth_hessian
    g hg K hK L (hL0.trans_le hL) (hdepth L hL)⟩

lemma referenceProfileNorm_eq_actualReferenceBeta (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) :
    referenceProfileNorm g lam δ R p L = actualReferenceBeta g L lam δ R p := rfl

/-- Degree floor: the profile norm is independent of the amplitude, so a degree threshold
gives the floor for every positive amplitude. -/
theorem referenceProfileBounds_exists_degree_floor
    (g : MatrixField) (K : Set R3) (L c0 c1 J1 J2 D : ℝ)
    (hc0 : 0 < c0) (hbounds : referenceProfileBounds g K L c0 c1 J1 J2 D) (betaMin : ℝ) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        max (1 : ℝ) betaMin ≤ referenceProfileNorm g lam δ R p L x := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (1 : ℝ) betaMin / c0)
  refine ⟨max q 2, le_max_right _ _, ?_⟩
  intro p hp lam hlam δ hδ hδ1 R hR x hx
  have hp1 : 1 ≤ p := le_trans (by norm_num) ((le_max_right q 2).trans hp)
  have hqp : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_max_left q 2).trans hp
  have hlarge : max (1 : ℝ) betaMin ≤ c0 * (p : ℝ) := by
    have h := (div_le_iff₀ hc0).mp (hq.le.trans hqp)
    simpa only [mul_comm] using h
  exact hlarge.trans (hbounds.1 lam hlam δ hδ hδ1 R hR p hp1 x hx).1

/-- All sufficiently small positive amplitudes, at a fixed conformal parameter and degree. -/
theorem exists_referenceRadius_small_amplitude_forall_le
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L) (p : ℕ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, 0 < R → R ≤ R0 →
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
        referenceRadius δ R p L x * actualReferenceBeta g L lam δ R p x ^ 2 ≤ ε := by
  obtain ⟨A1, A2, hA1, hA2, hamp⟩ :=
    exists_dilated_referenceRadius_uniform_amplitude_bounds_at g hg K hK L hL p hp
  have hden : 0 < A1 + A2 + 1 := by positivity
  refine ⟨ε / (A1 + A2 + 1), div_pos hε hden, ?_⟩
  intro R hR hR0 lam hlam δ hδ hδ1 x hx
  have hRA : R * (A1 + A2 + 1) ≤ ε := (le_div_iff₀ hden).mp hR0
  obtain ⟨h1, h2⟩ := hamp lam hlam δ hδ hδ1 R hR x hx
  have hR1 : R * A1 ≤ ε := by nlinarith [mul_pos hR hA1, mul_pos hR hA2]
  have hR2 : R * A2 ≤ ε := by nlinarith [mul_pos hR hA1, mul_pos hR hA2]
  unfold actualReferenceBeta
  exact ⟨h1.trans hR1, h2.trans hR2⟩

/-- Cofinal profile allocation in the consumer order: `L0`, every `L ≥ L0`, every floor, `p0`,
every `p ≥ p0`, every `ε`, `R0`, every positive amplitude `R ≤ R0`. Allocation only. -/
theorem exists_referenceProfile_allocation_forall_ge
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ betaMin : ℝ, ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∀ ε : ℝ, 0 < ε →
        ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, 0 < R → R ≤ R0 →
          ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
            max (1 : ℝ) betaMin ≤ actualReferenceBeta g L lam δ R p x ∧
            ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
            referenceRadius δ R p L x * actualReferenceBeta g L lam δ R p x ^ 2 ≤ ε := by
  obtain ⟨L0, hL0, hprofile⟩ := exists_referenceProfileBounds_forall_ge g hg K hK
  refine ⟨L0, hL0, ?_⟩
  intro L hLge betaMin
  have hL : 0 < L := hL0.trans_le hLge
  obtain ⟨c0, c1, J1, J2, D, hc0, -, -, -, -, hbounds⟩ := hprofile L hLge
  obtain ⟨p0, hp0, hfloor⟩ :=
    referenceProfileBounds_exists_degree_floor g K L c0 c1 J1 J2 D hc0 hbounds betaMin
  refine ⟨p0, hp0, ?_⟩
  intro p hp ε hε
  obtain ⟨R0, hR0, hsmall⟩ :=
    exists_referenceRadius_small_amplitude_forall_le g hg K hK L hL p (hp0.trans hp) ε hε
  refine ⟨R0, hR0, ?_⟩
  intro R hR hRR lam hlam δ hδ hδ1 x hx
  have hb := hfloor p hp lam hlam δ hδ hδ1 R hR x hx
  rw [referenceProfileNorm_eq_actualReferenceBeta] at hb
  exact ⟨hb, hsmall R hR hRR lam hlam δ hδ hδ1 x hx⟩

end OAI.AnisotropicCalderon.ConformalDepth
