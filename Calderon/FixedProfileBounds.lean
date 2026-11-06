import Calderon.ProfileDivergence
import Calderon.DilatedRadiusSmallness

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

theorem exists_dilated_referenceRadius_uniform_first_second_jet_bounds_at
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) (L : ℝ) (hL : 0 < L) :
    ∃ J1 J2 : ℝ, 0 < J1 ∧ 0 < J2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J1 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y))) x‖ ≤
          J2 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  obtain ⟨A, B, hA, hB, hjets⟩ := exists_referenceDepth_frechet_bounds_on_compact L K hK
  let a0 : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha0 : 0 < a0 := by
    dsimp [a0]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  let S : ℝ := (B / a0 + A ^ 2) / m ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨A / m + 1, S + 1, by positivity, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx
  rw [log_referenceRadius δ R p L hδ hR]
  let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (logProfile δ (Real.log R) p (referenceDepth L)) x
  have hbeta : 0 ≤ beta := Real.sqrt_nonneg _
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have ha := logSlope_pos δ (referenceDepth L x) hδ
  have halpha : 0 ≤ (p : ℝ) * logSlope δ (referenceDepth L x) := mul_nonneg (Nat.cast_nonneg p) ha.le
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  obtain ⟨hD1, hD2⟩ := hjets x hx
  have hbetaLower : (p : ℝ) * logSlope δ (referenceDepth L x) * m ≤ beta := by
    dsimp [beta]
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    exact mul_le_mul_of_nonneg_left hmin halpha
  constructor
  · have hdf : ‖fderiv ℝ (logProfile δ (Real.log R) p (referenceDepth L)) x‖ ≤
        (p : ℝ) * logSlope δ (referenceDepth L x) * A := by
      rw [fderiv_logProfile δ (Real.log R) p _ x hδ
        ((contDiff_referenceDepth L).differentiable (by simp) x)]
      simp only [profileDifferential, norm_smul, Real.norm_eq_abs, abs_of_nonneg halpha]
      exact mul_le_mul_of_nonneg_left hD1 halpha
    have hr := mul_le_mul_of_nonneg_left hbetaLower (show 0 ≤ A / m by positivity)
    have he : (A / m) * ((p : ℝ) * logSlope δ (referenceDepth L x) * m) =
        (p : ℝ) * logSlope δ (referenceDepth L x) * A := by field_simp
    rw [he] at hr
    exact hdf.trans (hr.trans (by change A / m * beta ≤ (A / m + 1) * beta; nlinarith))
  · have hDt := (contDiff_infty_iff_fderiv.mp (contDiff_referenceDepth L)).2
    have hnorm := norm_fderiv_fderiv_logProfile_le δ (Real.log R) p (referenceDepth L) x _ _ hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x).hasFDerivAt
      (hDt.differentiable (by simp) x).hasFDerivAt
      (Filter.Eventually.of_forall ((contDiff_referenceDepth L).differentiable (by simp)))
    have hterm1 := mul_le_mul_of_nonneg_left hD2 halpha
    have hterm2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hD1 2)
      (show 0 ≤ (p : ℝ) * (logSlope δ (referenceDepth L x)) ^ 2 by positivity)
    have hupper := hnorm.trans (add_le_add hterm1 hterm2)
    have hbase : ‖fderiv ℝ (fderiv ℝ (logProfile δ (Real.log R) p (referenceDepth L))) x‖ ≤
        S * beta ^ 2 := profile_second_norm_le_beta_square (p : ℝ) _ a0 m A B beta _ hpR ha0
      (logSlope_uniform_lower_bound δ _ T hδ hδ1 ht) hm hA hB hbetaLower hupper
    exact hbase.trans (by change S * beta ^ 2 ≤ (S + 1) * beta ^ 2; nlinarith [sq_nonneg beta])

theorem exists_dilated_referenceRadius_uniform_beta_derivative_bounds_at
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) (L : ℝ) (hL : 0 < L) :
    ∃ D : ℝ, 0 < D ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖fderiv ℝ (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y))) x‖ ≤
          D * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ∧
        ‖fderiv ℝ (fun y => (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun z => Real.log (referenceRadius δ R p L z)) y)⁻¹) x‖ ≤ D := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  obtain ⟨A, E, hA, hE, hjets⟩ := exists_referenceDepth_frechet_bounds_on_compact L K hK
  obtain ⟨B, hB, hbder⟩ := exists_dilatedReferenceDepth_uniform_normDerivative_bound g hg L hL K hK
  let a0 : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha0 : 0 < a0 := by
    dsimp [a0]
    apply one_div_pos.mpr
    have hl : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    linarith
  let S : ℝ := (B / a0 + (A + C) ^ 2) / m ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S + 1, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx
  rw [log_referenceRadius δ R p L hδ hR]
  let G := referenceMetric (dilatedMetric g lam) L
  let beta := metricDifferentialNorm G (logProfile δ (Real.log R) p (referenceDepth L))
  have hbase : ContDiff ℝ ∞ (metricDifferentialNorm G (referenceDepth L)) := by
    have h := (contDiff_dilatedReferenceDepth_metricNorm g hg L hL).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun y : R3 => (lam, y)))
    exact h
  have hbetaDer := hasFDerivAt_metricDifferentialNorm_logProfile G δ (Real.log R) p _
    (contDiff_referenceDepth L) x hδ (hbase.differentiable (by simp) x)
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have hD1 := (hjets x hx).1
  have hDb := hbder lam hlam x hx
  have ha := logSlope_pos δ (referenceDepth L x) hδ
  have halpha : 0 ≤ (p : ℝ) * logSlope δ (referenceDepth L x) := mul_nonneg (Nat.cast_nonneg p) ha.le
  have hbetaLower : (p : ℝ) * logSlope δ (referenceDepth L x) * m ≤ beta x := by
    dsimp [beta]
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    exact mul_le_mul_of_nonneg_left hmin halpha
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbetaPos : 0 < beta x := (show 0 < (p : ℝ) * logSlope δ (referenceDepth L x) * m by positivity).trans_le hbetaLower
  have hn := norm_fderiv_metricDifferentialNorm_logProfile_le G δ (Real.log R) p _
    (contDiff_referenceDepth L) x hδ (hbase.differentiable (by simp) x)
  have hproduct : ‖fderiv ℝ (referenceDepth L) x‖ * metricDifferentialNorm G (referenceDepth L) x ≤ A * C :=
    mul_le_mul hD1 hmax (Real.sqrt_nonneg _) hA
  have hAC : A * C ≤ (A + C) ^ 2 := by nlinarith [sq_nonneg A, sq_nonneg C]
  have hterm1 := mul_le_mul_of_nonneg_left (hproduct.trans hAC)
    (show 0 ≤ (p : ℝ) * (logSlope δ (referenceDepth L x)) ^ 2 by positivity)
  have hterm2 := mul_le_mul_of_nonneg_left hDb halpha
  have hupper : ‖fderiv ℝ beta x‖ ≤
      (p : ℝ) * logSlope δ (referenceDepth L x) * B +
      (p : ℝ) * (logSlope δ (referenceDepth L x)) ^ 2 * (A + C) ^ 2 := by
    nlinarith [hn, hterm1, hterm2]
  have hbound : ‖fderiv ℝ beta x‖ ≤ S * (beta x) ^ 2 :=
    profile_second_norm_le_beta_square (p : ℝ) _ a0 m (A + C) B (beta x) _ hpR ha0
      (logSlope_uniform_lower_bound δ _ T hδ hδ1 ht) hm (by positivity) hB hbetaLower hupper
  have hfinal : ‖fderiv ℝ beta x‖ ≤ (S + 1) * (beta x) ^ 2 :=
    hbound.trans (by nlinarith [sq_nonneg (beta x)])
  refine ⟨hfinal, ?_⟩
  have hinv : fderiv ℝ (fun y => (beta y)⁻¹) x =
      -((beta x) ^ 2)⁻¹ • fderiv ℝ beta x := by
    change fderiv ℝ ((fun y : ℝ => y⁻¹) ∘ beta) x = _
    rw [hbetaDer.fderiv]
    exact ((hasDerivAt_inv (ne_of_gt hbetaPos)).comp_hasFDerivAt x hbetaDer).fderiv
  change ‖fderiv ℝ (fun y => (beta y)⁻¹) x‖ ≤ S + 1
  rw [hinv]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_pow,
    abs_of_pos hbetaPos]
  have hr := mul_le_mul_of_nonneg_left hfinal (show 0 ≤ ((beta x) ^ 2)⁻¹ by positivity)
  have he : ((beta x) ^ 2)⁻¹ * ((S + 1) * (beta x) ^ 2) = S + 1 := by
    field_simp [ne_of_gt hbetaPos]
  rw [he] at hr
  exact hr

theorem exists_dilated_referenceRadius_uniform_amplitude_bounds_at
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) (L : ℝ) (hL : 0 < L) :
    ∀ p : ℕ, 2 ≤ p → ∃ A1 A2 : ℝ, 0 < A1 ∧ 0 < A2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ R * A1 ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ≤ R * A2 := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  obtain ⟨A, B, hA, hB, hjets⟩ := exists_referenceDepth_frechet_bounds_on_compact L K hK
  let M := Real.log (1 + Real.exp T)
  have hM : 0 < M := log_exp_add_one_pos T
  intro p hp
  let A1 := (p : ℝ) * M ^ (p - 1) * A + 1
  let A2 := (p : ℝ) ^ 2 * C ^ 2 * M ^ (p - 2) + 1
  have hA1 : 0 < A1 := by dsimp [A1]; positivity
  have hA2 : 0 < A2 := by dsimp [A2]; positivity
  refine ⟨A1, A2, hA1, hA2, ?_⟩
  intro lam hlam δ hδ hδ1 R hR x hx
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have hs := softplus_le_log_exp_upper δ (referenceDepth L x) T hδ hδ1 ht
  have hq := (softplus_derivative_lt_one δ (referenceDepth L x)).le
  have hs0 := (softplus_pos δ (referenceDepth L x) hδ).le
  have hq0 := (softplus_derivative_pos δ (referenceDepth L x)).le
  have hpow := pow_le_pow_left₀ hs0 hs (p - 1)
  have hn : ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤
      R * (p : ℝ) * M ^ (p - 1) * A := by
    rw [(hasFDerivAt_referenceRadius δ R p L x hδ).fderiv, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ R * (p : ℝ) * softplus δ (referenceDepth L x) ^ (p - 1) *
        (Real.exp (referenceDepth L x / δ) / (1 + Real.exp (referenceDepth L x / δ))))]
    have h1 := mul_le_mul hq (hjets x hx).1 (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul hpow h1 (by positivity) (pow_nonneg hM.le _)
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hR.le (Nat.cast_nonneg p))
    nlinarith [h3]
  refine ⟨hn.trans (by dsimp [A1]; nlinarith), ?_⟩
  rw [log_referenceRadius δ R p L hδ hR]
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
  have hr := radius_gradient_power_uniform_scale_bound δ _ T R C _ p 2 hδ hδ1 ht hR.le hC.le hb hp hbound
  exact hr.trans (by dsimp [A2, M]; nlinarith)

theorem exists_dilated_referenceRadius_uniform_small_amplitude_at
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) (L : ℝ) (hL : 0 < L)
    (p : ℕ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ≤ ε := by
  have hb := exists_dilated_referenceRadius_uniform_amplitude_bounds_at g hg K hK L hL
  obtain ⟨A1, A2, hA1, hA2, hbounds⟩ := hb p hp
  let R := ε / (A1 + A2 + 1)
  have hden : 0 < A1 + A2 + 1 := by positivity
  have hR : 0 < R := div_pos hε hden
  have he : R * (A1 + A2 + 1) = ε := by dsimp [R]; field_simp
  have h1 : R * A1 ≤ ε := by nlinarith
  have h2 : R * A2 ≤ ε := by nlinarith
  exact ⟨R, hR, fun lam hlam δ hδ hδ1 x hx =>
    ⟨((hbounds lam hlam δ hδ hδ1 R hR x hx).1).trans h1,
      ((hbounds lam hlam δ hδ hδ1 R hR x hx).2).trans h2⟩⟩

end OAI.AnisotropicCalderon.ConformalDepth
