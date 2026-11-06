import Calderon.DilatedProfileUniform
import Calderon.ProfileSecondBounds

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.ConformalDepth
open AngularPolynomial MetricOperator ConnectionError RadiusProfile

lemma exists_referenceDepth_frechet_bounds_on_compact (L : ℝ)
    (K : Set R3) (hK : IsCompact K) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ x ∈ K,
      ‖fderiv ℝ (referenceDepth L) x‖ ≤ A ∧
      ‖fderiv ℝ (fderiv ℝ (referenceDepth L)) x‖ ≤ B := by
  have hD := (contDiff_infty_iff_fderiv.mp (contDiff_referenceDepth L)).2
  have hDD := (contDiff_infty_iff_fderiv.mp hD).2
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hD.continuous.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hDD.continuous.continuousOn
  exact ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _,
    fun x hx => ⟨(hA x hx).trans (le_max_left _ _), (hB x hx).trans (le_max_left _ _)⟩⟩

lemma profile_second_norm_le_beta_square (P a a0 m A B beta n : ℝ)
    (hP : 1 ≤ P) (ha0 : 0 < a0) (ha : a0 ≤ a) (hm : 0 < m)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hbeta : P * a * m ≤ beta)
    (hn : n ≤ P * a * B + P * a ^ 2 * A ^ 2) :
    n ≤ ((B / a0 + A ^ 2) / m ^ 2) * beta ^ 2 := by
  have hapos : 0 < a := ha0.trans_le ha
  have hpa : a0 ≤ P * a := by nlinarith
  have halpha : 0 ≤ P * a := mul_nonneg (by linarith) hapos.le
  have hfirst : P * a * B ≤ (B / a0) * (P * a) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hpa (mul_nonneg halpha hB)
    have hr : P * a * B ≤ ((P * a) ^ 2 * B) / a0 :=
      (le_div_iff₀ ha0).mpr (by nlinarith [h])
    convert hr using 1 <;> ring
  have hp2 : P ≤ P ^ 2 := by nlinarith
  have hsecond : P * a ^ 2 * A ^ 2 ≤ (P * a) ^ 2 * A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ a ^ 2 * A ^ 2 by positivity)
    convert h using 1 <;> ring
  have hsq := pow_le_pow_left₀ (show 0 ≤ P * a * m by positivity) hbeta 2
  have halphaSq : (P * a) ^ 2 ≤ beta ^ 2 / m ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hm)).mpr (by nlinarith [hsq])
  calc
    n ≤ P * a * B + P * a ^ 2 * A ^ 2 := hn
    _ ≤ (B / a0) * (P * a) ^ 2 + (P * a) ^ 2 * A ^ 2 := add_le_add hfirst hsecond
    _ = (B / a0 + A ^ 2) * (P * a) ^ 2 := by ring
    _ ≤ (B / a0 + A ^ 2) * (beta ^ 2 / m ^ 2) :=
      mul_le_mul_of_nonneg_left halphaSq (by positivity)
    _ = ((B / a0 + A ^ 2) / m ^ 2) * beta ^ 2 := by ring

theorem exists_dilated_referenceRadius_uniform_first_second_jet_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L J1 J2 : ℝ, 0 < L ∧ 0 < J1 ∧ 0 < J2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J1 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ∧
        ‖fderiv ℝ (fderiv ℝ (fun y => Real.log (referenceRadius δ R p L y))) x‖ ≤
          J2 * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ 2 := by
  obtain ⟨L, hL, hdepth⟩ := exists_dilated_referenceDepth_uniform_strict_hessian_bound g hg K hK
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
  refine ⟨L, A / m + 1, S + 1, hL, by positivity, by positivity, ?_⟩
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

end OAI.AnisotropicCalderon.ConformalDepth
