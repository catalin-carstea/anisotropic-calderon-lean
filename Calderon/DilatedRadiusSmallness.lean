import Calderon.DilatedProfileBeta

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

lemma hasFDerivAt_referenceRadius (δ R : ℝ) (p : ℕ) (L : ℝ) (x : R3) (hδ : 0 < δ) :
    HasFDerivAt (referenceRadius δ R p L)
      ((R * (p : ℝ) * softplus δ (referenceDepth L x) ^ (p - 1) *
        (Real.exp (referenceDepth L x / δ) / (1 + Real.exp (referenceDepth L x / δ)))) •
        fderiv ℝ (referenceDepth L) x) x := by
  have h := (hasDerivAt_softplus δ (referenceDepth L x) (ne_of_gt hδ)).comp_hasFDerivAt x
    ((contDiff_referenceDepth L).differentiable (by simp) x).hasFDerivAt
  convert (h.pow p).const_smul R using 1 <;>
    simp [Function.comp_def, smul_smul, mul_assoc]
  funext y
  rfl

theorem exists_dilated_referenceRadius_uniform_amplitude_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ p : ℕ, 2 ≤ p → ∃ A1 A2 : ℝ, 0 < A1 ∧ 0 < A2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ x ∈ K,
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ R * A1 ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ≤ R * A2 := by
  obtain ⟨L, hL, hdepth⟩ := exists_dilated_referenceDepth_uniform_strict_hessian_bound g hg K hK
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  obtain ⟨A, B, hA, hB, hjets⟩ := exists_referenceDepth_frechet_bounds_on_compact L K hK
  let M := Real.log (1 + Real.exp T)
  have hM : 0 < M := log_exp_add_one_pos T
  refine ⟨L, hL, ?_⟩
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

theorem exists_dilated_referenceRadius_uniform_small_amplitude
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K)
    (p : ℕ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ L R : ℝ, 0 < L ∧ 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
        ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ ε ∧
        referenceRadius δ R p L x *
          metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ≤ ε := by
  obtain ⟨L, hL, hb⟩ := exists_dilated_referenceRadius_uniform_amplitude_bounds g hg K hK
  obtain ⟨A1, A2, hA1, hA2, hbounds⟩ := hb p hp
  let R := ε / (A1 + A2 + 1)
  have hden : 0 < A1 + A2 + 1 := by positivity
  have hR : 0 < R := div_pos hε hden
  have he : R * (A1 + A2 + 1) = ε := by dsimp [R]; field_simp
  have h1 : R * A1 ≤ ε := by nlinarith
  have h2 : R * A2 ≤ ε := by nlinarith
  exact ⟨L, R, hL, hR, fun lam hlam δ hδ hδ1 x hx =>
    ⟨((hbounds lam hlam δ hδ hδ1 R hR x hx).1).trans h1,
      ((hbounds lam hlam δ hδ hδ1 R hR x hx).2).trans h2⟩⟩

end OAI.AnisotropicCalderon.ConformalDepth
