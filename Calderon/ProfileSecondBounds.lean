import Calderon.ProfileChain

namespace OAI.AnisotropicCalderon.RadiusProfile
open scoped Topology

theorem abs_logSlopeDerivative_le_sq (δ t : ℝ) (hδ : 0 < δ) :
    |logSlopeDerivative δ t| ≤ (logSlope δ t)^2 := by
  have hL := log_exp_add_one_pos (t/δ)
  have he : 0 < 1+Real.exp (t/δ) := by positivity
  have hidentity : logSlopeDerivative δ t + (logSlope δ t)^2 =
      Real.exp (t/δ)*Real.log (1+Real.exp (t/δ)) /
        (δ^2*(1+Real.exp (t/δ))^2*(Real.log (1+Real.exp (t/δ)))^2) := by
    unfold logSlopeDerivative logSlope
    field_simp [ne_of_gt hδ, ne_of_gt hL, ne_of_gt he]
    <;> ring
  have hpos : 0 < logSlopeDerivative δ t + (logSlope δ t)^2 := by
    rw [hidentity]
    positivity
  rw [abs_of_neg (logSlopeDerivative_neg δ t hδ)]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_profileSecondDifferential_le (δ : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hδ : 0 < δ) :
    ‖profileSecondDifferential δ p t x T H‖ ≤
      (p : ℝ)*logSlope δ (t x)*‖H‖ +
        (p : ℝ)*(logSlope δ (t x))^2*‖T‖^2 := by
  have ha : 0 ≤ (p : ℝ)*logSlope δ (t x) :=
    mul_nonneg (Nat.cast_nonneg p) (le_of_lt (logSlope_pos δ (t x) hδ))
  have hbound := mul_le_mul_of_nonneg_left (abs_logSlopeDerivative_le_sq δ (t x) hδ)
    (Nat.cast_nonneg p)
  have hn := norm_add_le
    (((p : ℝ)*logSlope δ (t x)) • H)
    ((((p : ℝ)*logSlopeDerivative δ (t x)) • T).smulRight T)
  have h₁ := ContinuousLinearMap.opNorm_smul_le ((p : ℝ)*logSlope δ (t x)) H
  have h₂ := ContinuousLinearMap.opNorm_smul_le ((p : ℝ)*logSlopeDerivative δ (t x)) T
  rw [Real.norm_eq_abs, abs_of_nonneg ha] at h₁
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg p)] at h₂
  rw [ContinuousLinearMap.norm_smulRight_apply] at hn
  have h₂' := mul_le_mul_of_nonneg_right h₂ (norm_nonneg T)
  have hnorm := mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖T‖)
  unfold profileSecondDifferential
  nlinarith [hn, hnorm, h₁, h₂']

theorem norm_fderiv_fderiv_logProfile_le (δ c : ℝ) (p : ℕ) (t : E → ℝ)
    (x : E) (T : E →L[ℝ] ℝ) (H : E →L[ℝ] (E →L[ℝ] ℝ)) (hδ : 0 < δ)
    (ht : HasFDerivAt t T x) (hH : HasFDerivAt (fderiv ℝ t) H x)
    (hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ t y) :
    ‖fderiv ℝ (fderiv ℝ (logProfile δ c p t)) x‖ ≤
      (p : ℝ)*logSlope δ (t x)*‖H‖ +
        (p : ℝ)*(logSlope δ (t x))^2*‖T‖^2 := by
  rw [(hasFDerivAt_fderiv_logProfile δ c p t x T H hδ ht hH hnear).fderiv]
  exact norm_profileSecondDifferential_le δ p t x T H hδ

#print axioms abs_logSlopeDerivative_le_sq
#print axioms norm_fderiv_fderiv_logProfile_le
end OAI.AnisotropicCalderon.RadiusProfile
