import Calderon.JacobiIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Set MeasureTheory

namespace OAI.AnisotropicCalderon.JacobiIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_leftMoment_le (f : ℝ → E) (t C : ℝ) (ht : t ∈ Icc 0 1)
    (hC : 0 ≤ C) (hf : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ C) :
    ‖leftMoment f t‖ ≤ C * t^2 / 2 := by
  have hint : IntervalIntegrable (fun s : ℝ => s*C) volume 0 t :=
    (continuous_id.mul continuous_const).intervalIntegrable _ _
  have hb : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → ‖s • f s‖ ≤ s*C :=
    Filter.Eventually.of_forall fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le,hs.2.trans ht.2⟩) hs.1.le
  have h := intervalIntegral.norm_integral_le_of_norm_le ht.1 hb hint
  have hi : (∫ s in (0:ℝ)..t, s*C) = C * t^2 / 2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  simpa only [leftMoment, hi] using h

lemma norm_rightMoment_le (f : ℝ → E) (t C : ℝ) (ht : t ∈ Icc 0 1)
    (hC : 0 ≤ C) (hf : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ C) :
    ‖rightMoment f t‖ ≤ C * (1-t)^2 / 2 := by
  have hc : Continuous (fun s : ℝ => (1-s)*C) :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hint : IntervalIntegrable (fun s : ℝ => (1-s)*C) volume t 1 :=
    hc.intervalIntegrable t 1
  have hb : ∀ᵐ s : ℝ, s ∈ Ioc t 1 → ‖(1-s) • f s‖ ≤ (1-s)*C :=
    Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (hf s ⟨ht.1.trans hs.1.le,hs.2⟩) hs0
  have h := intervalIntegral.norm_integral_le_of_norm_le ht.2 hb hint
  have hi : (∫ s in t..(1:ℝ), (1-s)*C) = C * (1-t)^2 / 2 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume t 1 :=
      continuous_const.intervalIntegrable t 1
    have hid : IntervalIntegrable (fun s : ℝ => s) volume t 1 :=
      continuous_id.intervalIntegrable t 1
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub hconst hid,
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  simpa only [rightMoment, hi] using h

theorem norm_sub_affine_le (j j' f : ℝ → E) (t C : ℝ) (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ C) :
    ‖j t - ((1-t) • j 0 + t • j 1)‖ ≤ C / 8 := by
  have he : j t - ((1-t) • j 0 + t • j 1) =
      -((1-t) • leftMoment f t + t • rightMoment f t) := by
    rw [endpoint_representation j j' f t ht hj hj' hf]
    module
  rw [he,norm_neg]
  have h1 := norm_leftMoment_le f t C ht hC hbound
  have h2 := norm_rightMoment_le f t C ht hC hbound
  have h3 := norm_add_le ((1-t) • leftMoment f t) (t • rightMoment f t)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1] at h3
  have h4 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht.2)
  have h5 := mul_le_mul_of_nonneg_left h2 ht.1
  have h6 : C * (t-(1/2:ℝ))^2 ≥ 0 := mul_nonneg hC (sq_nonneg _)
  nlinarith

theorem norm_derivative_sub_endpoints_le (j j' f : ℝ → E) (t C : ℝ)
    (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ C) :
    ‖j' t - (j 1 - j 0)‖ ≤ C / 2 := by
  rw [endpoint_derivative_representation j j' f t ht hj hj' hf]
  have h1 := norm_leftMoment_le f t C ht hC hbound
  have h2 := norm_rightMoment_le f t C ht hC hbound
  have h3 := norm_sub_le (leftMoment f t) (rightMoment f t)
  have h4 : 0 ≤ C*t*(1-t) := mul_nonneg (mul_nonneg hC ht.1) (sub_nonneg.mpr ht.2)
  nlinarith

#print axioms norm_sub_affine_le
#print axioms norm_derivative_sub_endpoints_le
end OAI.AnisotropicCalderon.JacobiIntegral
