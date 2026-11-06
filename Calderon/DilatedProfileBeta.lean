import Calderon.DilatedProfileJets
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

lemma contDiff_dilatedReferenceDepth_metricNorm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (hL : 0 < L) : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      metricDifferentialNorm (referenceMetric (dilatedMetric g z.1) L) (referenceDepth L) z.2) := by
  have hQ : ContDiff ℝ ∞ (fun z : ℝ × R3 => inverseMetricOperator g (z.1 • z.2)) :=
    (contDiff_inverseMetricOperator g hg).comp (contDiff_fst.smul contDiff_snd)
  have ha : ContDiff ℝ ∞ (fun z : ℝ × R3 => Real.exp (2 * L * referenceCoordinateDepth z.2)) :=
    (contDiff_const.mul (contDiff_referenceCoordinateDepth.comp contDiff_snd)).exp
  have hI : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) := by
    have he : (fun z : ℝ × R3 => inverseMetricOperator (referenceMetric (dilatedMetric g z.1) L) z.2) =
        fun z => Real.exp (2 * L * referenceCoordinateDepth z.2) • inverseMetricOperator g (z.1 • z.2) :=
      funext (fun z => inverseMetricOperator_dilatedReference g hg z.1 L z.2)
    rw [he]
    exact ha.smul hQ
  have hG : ContDiff ℝ ∞ (fun z : ℝ × R3 => gradient (referenceDepth L) z.2) :=
    ((contDiff_referenceDepth L).gradient_right (m := ∞) (by simp)).comp contDiff_snd
  apply ((hI.clm_apply hG).inner ℝ hG).sqrt
  intro z
  have hp : ∀ y, (referenceMetric (dilatedMetric g z.1) L y).PosDef :=
    fun y => EnergyBridge.conformalMatrix_posDef _ _ (dilatedMetric_posDef g hg z.1) y
  have h := metricDifferentialNorm_pos _ hp _ z.2
    (fderiv_referenceDepth_ne_zero L (ne_of_gt hL) z.2)
  exact ne_of_gt (Real.sqrt_pos.mp h)

lemma exists_dilatedReferenceDepth_uniform_normDerivative_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖fderiv ℝ (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (referenceDepth L)) x‖ ≤ D := by
  let F : ℝ × R3 → ℝ := fun z =>
    metricDifferentialNorm (referenceMetric (dilatedMetric g z.1) L) (referenceDepth L) z.2
  have hF : ContDiff ℝ ∞ F := contDiff_dilatedReferenceDepth_metricNorm g hg L hL
  have he : (fun z : ℝ × R3 => fderiv ℝ
      (metricDifferentialNorm (referenceMetric (dilatedMetric g z.1) L) (referenceDepth L)) z.2) =
      fun z => (fderiv ℝ F z).comp (ContinuousLinearMap.inr ℝ ℝ R3) := by
    funext z
    have hpair : HasFDerivAt (fun y : R3 => (z.1, y))
        (ContinuousLinearMap.inr ℝ ℝ R3) z.2 := hasFDerivAt_prodMk_right z.1 z.2
    exact (((hF.differentiable (by simp) z).hasFDerivAt).comp z.2 hpair).fderiv
  have hcont : Continuous (fun z : ℝ × R3 => fderiv ℝ
      (metricDifferentialNorm (referenceMetric (dilatedMetric g z.1) L) (referenceDepth L)) z.2) := by
    rw [he]
    exact ((contDiff_infty_iff_fderiv.mp hF).2.continuous).clm_comp continuous_const
  obtain ⟨D, hD⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max D 0, le_max_right _ _, fun lam hlam x hx =>
    (hD (lam, x) ⟨hlam, hx⟩).trans (le_max_left _ _)⟩

lemma hasFDerivAt_metricDifferentialNorm_logProfile (g : MatrixField) (δ c : ℝ) (p : ℕ)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (x : R3) (hδ : 0 < δ)
    (hb : DifferentiableAt ℝ (metricDifferentialNorm g u) x) :
    HasFDerivAt (metricDifferentialNorm g (logProfile δ c p u))
      ((metricDifferentialNorm g u x) •
        (((p : ℝ) * logSlopeDerivative δ (u x)) • fderiv ℝ u x) +
        ((p : ℝ) * logSlope δ (u x)) • fderiv ℝ (metricDifferentialNorm g u) x) x := by
  have he : metricDifferentialNorm g (logProfile δ c p u) =
      fun y => ((p : ℝ) * logSlope δ (u y)) * metricDifferentialNorm g u y :=
    funext (fun y => metricDifferentialNorm_logProfile g δ c p u y hδ
      (hu.differentiable (by simp) y))
  rw [he]
  have ha := ((hasDerivAt_logSlope δ (u x) hδ).comp_hasFDerivAt x
    (hu.differentiable (by simp) x).hasFDerivAt).const_smul (p : ℝ)
  convert ha.mul hb.hasFDerivAt using 1 <;>
    simp [Function.comp_def, Pi.smul_apply, smul_eq_mul, smul_smul, add_comm]
  funext y
  simp [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc]

lemma norm_fderiv_metricDifferentialNorm_logProfile_le (g : MatrixField) (δ c : ℝ) (p : ℕ)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (x : R3) (hδ : 0 < δ)
    (hb : DifferentiableAt ℝ (metricDifferentialNorm g u) x) :
    ‖fderiv ℝ (metricDifferentialNorm g (logProfile δ c p u)) x‖ ≤
      (p : ℝ) * (logSlope δ (u x)) ^ 2 * ‖fderiv ℝ u x‖ * metricDifferentialNorm g u x +
      (p : ℝ) * logSlope δ (u x) * ‖fderiv ℝ (metricDifferentialNorm g u) x‖ := by
  rw [(hasFDerivAt_metricDifferentialNorm_logProfile g δ c p u hu x hδ hb).fderiv]
  have hbn : 0 ≤ metricDifferentialNorm g u x := Real.sqrt_nonneg _
  have ha : 0 ≤ (p : ℝ) * logSlope δ (u x) :=
    mul_nonneg (Nat.cast_nonneg p) (logSlope_pos δ (u x) hδ).le
  have hn := norm_add_le ((metricDifferentialNorm g u x) •
      (((p : ℝ) * logSlopeDerivative δ (u x)) • fderiv ℝ u x))
    (((p : ℝ) * logSlope δ (u x)) • fderiv ℝ (metricDifferentialNorm g u) x)
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hbn,
    abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p), abs_of_nonneg ha] at hn
  have hs := mul_le_mul_of_nonneg_right (abs_logSlopeDerivative_le_sq δ (u x) hδ)
    (show 0 ≤ metricDifferentialNorm g u x * (p : ℝ) * ‖fderiv ℝ u x‖ by positivity)
  nlinarith [hn, hs]

theorem exists_dilated_referenceRadius_uniform_beta_derivative_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L D : ℝ, 0 < L ∧ 0 < D ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖fderiv ℝ (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun y => Real.log (referenceRadius δ R p L y))) x‖ ≤
          D * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 ∧
        ‖fderiv ℝ (fun y => (metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
          (fun z => Real.log (referenceRadius δ R p L z)) y)⁻¹) x‖ ≤ D := by
  obtain ⟨L, hL, hdepth⟩ := exists_dilated_referenceDepth_uniform_strict_hessian_bound g hg K hK
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
  refine ⟨L, S + 1, hL, by positivity, ?_⟩
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

end OAI.AnisotropicCalderon.ConformalDepth
