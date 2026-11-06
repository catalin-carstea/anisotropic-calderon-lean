import Calderon.RadiusProfileBounds
import Calderon.ProfileChain
import Mathlib.Tactic

namespace OAI.AnisotropicCalderon.RadiusProfile

lemma one_lt_logSlope_mul_delta_add_softplus (δ s : ℝ) (hδ : 0 < δ) :
    1 < logSlope δ s * (δ + softplus δ s) := by
  have he := Real.exp_pos (s/δ)
  have hL := log_exp_add_one_pos (s/δ)
  have hLe : Real.log (1 + Real.exp (s/δ)) < Real.exp (s/δ) := by
    have h := Real.log_lt_sub_one_of_pos
      (by positivity : 0 < 1 + Real.exp (s/δ))
      (by linarith : 1 + Real.exp (s/δ) ≠ 1)
    linarith
  unfold logSlope softplus
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (by positivity :
    0 < δ * (1 + Real.exp (s/δ)) * Real.log (1 + Real.exp (s/δ)))).2
  nlinarith [mul_pos hδ (sub_pos.mpr hLe)]

lemma logSlope_uniform_lower_bound (δ s T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : s ≤ T) :
    1 / (1 + Real.log (1 + Real.exp T)) ≤ logSlope δ s := by
  have hU : 0 < 1 + Real.log (1 + Real.exp T) := by
    linarith [log_exp_add_one_pos T]
  have ha := logSlope_pos δ s hδ
  have hb : δ + softplus δ s ≤ 1 + Real.log (1 + Real.exp T) := by
    linarith [softplus_le_log_exp_upper δ s T hδ hδ1 hs]
  apply (div_le_iff₀ hU).2
  exact le_trans (le_of_lt (one_lt_logSlope_mul_delta_add_softplus δ s hδ))
    (mul_le_mul_of_nonneg_left hb (le_of_lt ha))

theorem norm_fderiv_logProfile_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (p : ℕ) (c : ℝ) (t : E → ℝ) (x : E)
    (D : E →L[ℝ] ℝ) (m T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : HasFDerivAt t D x)
    (hT : t x ≤ T) (hm : 0 ≤ m) (hD : m ≤ ‖D‖) :
    (p : ℝ) * m / (1 + Real.log (1 + Real.exp T)) ≤
      ‖fderiv ℝ (logProfile δ c p t) x‖ := by
  rw [(hasFDerivAt_logProfile δ c p t x D hδ ht).fderiv, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg p)
      (le_of_lt (logSlope_pos δ (t x) hδ)))]
  have ha := logSlope_uniform_lower_bound δ (t x) T hδ hδ1 hT
  have hn : (p : ℝ) * (1 / (1 + Real.log (1 + Real.exp T))) * m ≤
      (p : ℝ) * logSlope δ (t x) * ‖D‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg p)) hD hm
      (mul_nonneg (Nat.cast_nonneg p) (le_of_lt (logSlope_pos δ (t x) hδ)))
  convert hn using 1 <;> ring

theorem exists_profile_exponent (m U B : ℝ) (hm : 0 < m) (hU : 0 < U) :
    ∃ p : ℕ, 2 ≤ p ∧ B < (p : ℝ) * m / U := by
  obtain ⟨p, hp⟩ := exists_nat_gt (max 2 (B * U / m))
  refine ⟨p, ?_, ?_⟩
  · have h : (2 : ℝ) ≤ (p : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) hp)
    exact_mod_cast h
  · apply (lt_div_iff₀ hU).2
    have h : B * U / m < (p : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hp
    exact (div_lt_iff₀ hm).mp h

#print axioms logSlope_uniform_lower_bound
#print axioms norm_fderiv_logProfile_lower_bound
#print axioms exists_profile_exponent
end OAI.AnisotropicCalderon.RadiusProfile
