import Calderon.SmoothSobolevBridge

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.AngularPolynomial

lemma weighted_gradient_norm_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k beta z : ℝ) (v a : E) (hk : 0 ≤ k) (hb : 0 < beta)
    (ha : z ≠ 0 → ‖a‖ ^ 2 ≤ beta ^ 2) :
    (k / beta) * ‖v‖ ^ 2 ≤
      2 * (k / beta) * ‖v + (k * z) • a‖ ^ 2 + 2 * k ^ 3 * beta * z ^ 2 := by
  have hq : ‖(k * z) • a‖ ^ 2 ≤ k ^ 2 * beta ^ 2 * z ^ 2 := by
    by_cases hz : z = 0
    · simp [hz]
    · have he : ‖(k * z) • a‖ ^ 2 = k ^ 2 * z ^ 2 * ‖a‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      rw [he]
      have h := mul_le_mul_of_nonneg_left (ha hz) (mul_nonneg (sq_nonneg k) (sq_nonneg z))
      nlinarith
  have ht : ‖v‖ ≤ ‖v + (k * z) • a‖ + ‖(k * z) • a‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (v + (k * z) • a) ((k * z) • a)
  have hs := (sq_le_sq₀ (norm_nonneg v)
    (add_nonneg (norm_nonneg (v + (k * z) • a)) (norm_nonneg ((k * z) • a)))).2 ht
  have hd : ‖v‖ ^ 2 ≤ 2 * ‖v + (k * z) • a‖ ^ 2 + 2 * ‖(k * z) • a‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v + (k * z) • a‖ - ‖(k * z) • a‖)]
  have hw : 0 ≤ k / beta := div_nonneg hk hb.le
  calc
    (k / beta) * ‖v‖ ^ 2 ≤
        (k / beta) * (2 * ‖v + (k * z) • a‖ ^ 2 + 2 * ‖(k * z) • a‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hd hw
    _ ≤ 2 * (k / beta) * ‖v + (k * z) • a‖ ^ 2 +
        2 * (k / beta) * (k ^ 2 * beta ^ 2 * z ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw)
      nlinarith
    _ = 2 * (k / beta) * ‖v + (k * z) • a‖ ^ 2 + 2 * k ^ 3 * beta * z ^ 2 := by
      field_simp [ne_of_gt hb]

lemma gradient_hasCompactSupport (u : R3 → ℝ) (hc : HasCompactSupport u) :
    HasCompactSupport (gradient u) := by
  change HasCompactSupport ((InnerProductSpace.toDual ℝ R3).symm ∘ fderiv ℝ u)
  exact (hc.fderiv (𝕜 := ℝ)).comp_left (map_zero (InnerProductSpace.toDual ℝ R3).symm)

lemma compact_norm_profile_integrable {E : Type*} [NormedAddCommGroup E]
    (b : R3 → ℝ) (v : R3 → E) (hb : Continuous b) (hv : Continuous v)
    (hc : HasCompactSupport v) : Integrable (fun x => b x * ‖v x‖ ^ 2) := by
  have hs : HasCompactSupport (fun x : R3 => ‖v x‖ ^ 2) := by
    change HasCompactSupport ((fun y : E => ‖y‖ ^ 2) ∘ v)
    exact hc.comp_left (by simp)
  exact (hb.mul (hv.norm.pow 2)).integrable_of_hasCompactSupport hs.mul_left

theorem compact_euclidean_gradient_comparison (k : ℝ) (hk : 0 ≤ k)
    (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (a : R3 → R3) (ha : Continuous a) (beta : R3 → ℝ) (hb : Continuous beta)
    (hpos : ∀ x, 0 < beta x) (hsize : ∀ x, u x ≠ 0 → ‖a x‖ ^ 2 ≤ beta x ^ 2) :
    (∫ x : R3, (k / beta x) * ‖gradient u x‖ ^ 2) ≤
      2 * (∫ x : R3, (k / beta x) * ‖gradient u x + (k * u x) • a x‖ ^ 2) +
        2 * k ^ 3 * (∫ x : R3, beta x * u x ^ 2) := by
  have hg : Continuous (gradient u) := (hu.gradient_right (m := 0) (by simp)).continuous
  have hcg := gradient_hasCompactSupport u hc
  have hw : Continuous (fun x => k / beta x) :=
    continuous_const.div hb (fun x => ne_of_gt (hpos x))
  have hp : Continuous (fun x => gradient u x + (k * u x) • a x) :=
    hg.add ((continuous_const.mul hu.continuous).smul ha)
  have hcp : HasCompactSupport (fun x => gradient u x + (k * u x) • a x) :=
    hcg.add ((show HasCompactSupport (fun x : R3 => k * u x) from hc.mul_left).smul_right)
  have hleft := compact_norm_profile_integrable _ _ hw hg hcg
  have hplus := compact_norm_profile_integrable _ _ hw hp hcp
  have hmass : Integrable (fun x : R3 => beta x * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      compact_norm_profile_integrable beta u hb hu.continuous hc
  have h := integral_mono hleft ((hplus.const_mul 2).add (hmass.const_mul (2 * k ^ 3)))
    (fun x => by
      change (k / beta x) * ‖gradient u x‖ ^ 2 ≤
        2 * ((k / beta x) * ‖gradient u x + (k * u x) • a x‖ ^ 2) +
          (2 * k ^ 3) * (beta x * u x ^ 2)
      simpa only [mul_assoc] using
        weighted_gradient_norm_sq_le k (beta x) (u x) (gradient u x) (a x)
          hk (hpos x) (hsize x))
  change (∫ x : R3, (k / beta x) * ‖gradient u x‖ ^ 2) ≤
    ∫ x : R3, 2 * ((k / beta x) * ‖gradient u x + (k * u x) • a x‖ ^ 2) +
      (2 * k ^ 3) * (beta x * u x ^ 2) at h
  rw [integral_add (hplus.const_mul 2) (hmass.const_mul (2 * k ^ 3))] at h
  simpa only [integral_const_mul] using h

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.weighted_gradient_norm_sq_le
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.gradient_hasCompactSupport
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_euclidean_gradient_comparison
