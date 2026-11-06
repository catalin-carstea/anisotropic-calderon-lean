import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/- Exact Euclidean part of the shrinking-sphere test.
   Curved and metric-perturbation application bounds remain separate obligations. -/
namespace OAI.AnisotropicCalderon.ShrinkingGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def perpendicularComponent (ω x : E) : E := x - inner ℝ ω x • ω

lemma norm_perpendicularComponent_sq (ω x : E) (hω : ‖ω‖ = 1) :
    ‖perpendicularComponent ω x‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ ω x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [perpendicularComponent, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq,
    hω, one_pow, mul_one]
  rw [real_inner_comm x ω]
  ring

lemma inner_perpendicularComponent (ω x y : E) (hω : ‖ω‖ = 1) :
    inner ℝ (perpendicularComponent ω x) (perpendicularComponent ω y) =
      inner ℝ x y - inner ℝ ω x * inner ℝ ω y := by
  simp only [perpendicularComponent, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq,
    hω, one_pow, mul_one]
  rw [real_inner_comm x ω]
  ring

lemma perpendicularComponent_sub (ω x y : E) :
    perpendicularComponent ω (x - y) =
      perpendicularComponent ω x - perpendicularComponent ω y := by
  simp only [perpendicularComponent, inner_sub_right]
  module

lemma perpendicularComponent_smul (ω x : E) (c : ℝ) :
    perpendicularComponent ω (c • x) = c • perpendicularComponent ω x := by
  simp only [perpendicularComponent, inner_smul_right]
  module

lemma perpendicularComponent_self (ω : E) (hω : ‖ω‖ = 1) :
    perpendicularComponent ω ω = 0 := by
  simp [perpendicularComponent, hω]

lemma perpendicularComponent_eq_self (ω v : E) (h : inner ℝ ω v = 0) :
    perpendicularComponent ω v = v := by simp [perpendicularComponent, h]

lemma residual_factor_nonneg (k x : ℝ) (hx : 1 / 2 ≤ x) (hxk : x ≤ k) :
    0 ≤ k ^ 2 - k + x - x ^ 2 := by
  have h₁ : 0 ≤ k - x := sub_nonneg.mpr hxk
  have h₂ : 0 ≤ k + x - 1 := by linarith
  nlinarith [mul_nonneg h₁ h₂]

lemma norm_perpendicularComponent_ge_normalized_inner
    (ω u w : E) (hω : ‖ω‖ = 1) (hu : 0 < ‖u‖ ^ 2)
    (hm : 0 ≤ inner ℝ ω u) (huw : inner ℝ u w = 0)
    (hw : ‖w‖ ^ 2 = 1 / ‖u‖ ^ 2) :
    inner ℝ ω u / ‖u‖ ^ 2 ≤ ‖perpendicularComponent ω w‖ := by
  let D : ℝ := ‖u‖ ^ 2
  let m : ℝ := inner ℝ ω u
  let z : ℝ := inner ℝ ω w
  have hD : 0 < D := hu
  have hDne : D ≠ 0 := ne_of_gt hD
  have hz : inner ℝ (ω - (m / D) • u) w = z := by
    simp [inner_sub_left, inner_smul_left, huw, z]
  have hn : ‖ω - (m / D) • u‖ ^ 2 = 1 - m ^ 2 / D := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq, hω, one_pow]
    have hcomm : inner ℝ u ω = m := (real_inner_comm u ω).symm
    rw [hcomm]
    change 1 - m / D * m - m / D * (m - m / D * D) = _
    field_simp
    ring
  have hcs := real_inner_mul_inner_self_le (ω - (m / D) • u) w
  rw [hz, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn, hw] at hcs
  change z * z ≤ (1 - m ^ 2 / D) * (1 / D) at hcs
  have hp := norm_perpendicularComponent_sq ω w hω
  rw [hw] at hp
  change ‖perpendicularComponent ω w‖ ^ 2 = 1 / D - z ^ 2 at hp
  have hsq : (m / D) ^ 2 ≤ ‖perpendicularComponent ω w‖ ^ 2 := by
    have hmul := (mul_le_mul_of_nonneg_right hcs (sq_nonneg D))
    field_simp [hDne] at hmul hp ⊢
    nlinarith [congrArg (fun s : ℝ => D * s) hp]
  have hmn : 0 ≤ m / D := div_nonneg hm (le_of_lt hD)
  nlinarith [norm_nonneg (perpendicularComponent ω w)]

lemma norm_smul_sq (c : ℝ) (x : E) : ‖c • x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma residual_identity (ω u v w : E) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (hωv : inner ℝ ω v = 0) (huw : inner ℝ u w = 0)
    (hD : ‖u‖ ^ 2 ≠ 0) (hw : ‖w‖ ^ 2 = 1 / ‖u‖ ^ 2) :
    ‖perpendicularComponent ω (ω - (1 / ‖u‖ ^ 2) • u)‖ ^ 2 +
      ‖perpendicularComponent ω (v - w)‖ ^ 2 -
      (inner ℝ (u - ω) ((1 / ‖u‖ ^ 2) • u)) ^ 2 -
      (inner ℝ (u - ω) w) ^ 2 =
    2 * (‖perpendicularComponent ω w‖ ^ 2 - inner ℝ v w +
      inner ℝ ω u / ‖u‖ ^ 2 - (inner ℝ ω u / ‖u‖ ^ 2) ^ 2) := by
  have hreal : perpendicularComponent ω (ω - (1 / ‖u‖ ^ 2) • u) =
      -(1 / ‖u‖ ^ 2) • perpendicularComponent ω u := by
    rw [perpendicularComponent_sub, perpendicularComponent_self ω hω,
      perpendicularComponent_smul]
    module
  rw [hreal, norm_smul_sq, perpendicularComponent_sub,
    perpendicularComponent_eq_self ω v hωv, norm_sub_sq_real, hv, one_pow]
  have hinner : inner ℝ v (perpendicularComponent ω w) = inner ℝ v w := by
    simp only [perpendicularComponent, inner_sub_right, inner_smul_right]
    have hvω : inner ℝ v ω = 0 := by rw [real_inner_comm]; exact hωv
    simp [hvω]
  rw [hinner, norm_perpendicularComponent_sq ω u hω]
  simp only [inner_sub_left, inner_smul_right, huw, zero_sub,
    real_inner_self_eq_norm_sq]
  have hp := norm_perpendicularComponent_sq ω w hω
  rw [hw] at hp
  rw [hp]
  have hn0 : ‖u‖ ≠ 0 := fun h => hD (by simp [h])
  field_simp [hn0]
  ring

theorem residual_nonneg_of_norm_sq_le_two_inner
    (ω u v w : E) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (hωv : inner ℝ ω v = 0) (huw : inner ℝ u w = 0)
    (hu : 0 < ‖u‖ ^ 2) (hm : 0 ≤ inner ℝ ω u)
    (hsmall : ‖u‖ ^ 2 ≤ 2 * inner ℝ ω u)
    (hw : ‖w‖ ^ 2 = 1 / ‖u‖ ^ 2) :
    0 ≤ ‖perpendicularComponent ω (ω - (1 / ‖u‖ ^ 2) • u)‖ ^ 2 +
      ‖perpendicularComponent ω (v - w)‖ ^ 2 -
      (inner ℝ (u - ω) ((1 / ‖u‖ ^ 2) • u)) ^ 2 -
      (inner ℝ (u - ω) w) ^ 2 := by
  rw [residual_identity ω u v w hω hv hωv huw (ne_of_gt hu) hw]
  have hxk := norm_perpendicularComponent_ge_normalized_inner ω u w hω hu hm huw hw
  have hx : 1 / 2 ≤ inner ℝ ω u / ‖u‖ ^ 2 := by
    apply (le_div_iff₀ hu).2
    linarith
  have hi : inner ℝ v w ≤ ‖perpendicularComponent ω w‖ := by
    have hvω : inner ℝ v ω = 0 := by rw [real_inner_comm]; exact hωv
    have hcs := real_inner_le_norm v (perpendicularComponent ω w)
    simpa [perpendicularComponent, inner_sub_right, inner_smul_right, hvω, hv] using hcs
  have hfactor := residual_factor_nonneg ‖perpendicularComponent ω w‖
    (inner ℝ ω u / ‖u‖ ^ 2) hx hxk
  nlinarith

theorem shrinking_sphere_residual_nonneg (ω b v w : E)
    (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1) (hωv : inner ℝ ω v = 0)
    (hb : ‖b‖ ≤ 1 / 4) (huw : inner ℝ (ω + b) w = 0)
    (hw : ‖w‖ ^ 2 = 1 / ‖ω + b‖ ^ 2) :
    0 ≤ ‖perpendicularComponent ω (ω - (1 / ‖ω + b‖ ^ 2) • (ω + b))‖ ^ 2 +
      ‖perpendicularComponent ω (v - w)‖ ^ 2 -
      (inner ℝ b ((1 / ‖ω + b‖ ^ 2) • (ω + b))) ^ 2 -
      (inner ℝ b w) ^ 2 := by
  have ha : |inner ℝ ω b| ≤ 1 / 4 := by
    have hcs := abs_real_inner_le_norm ω b
    simpa [hω] using hcs.trans (by simpa [hω] using hb)
  have hnorm : ‖ω + b‖ ^ 2 = 1 + 2 * inner ℝ ω b + ‖b‖ ^ 2 := by
    simpa [hω] using norm_add_sq_real ω b
  have hm : inner ℝ ω (ω + b) = 1 + inner ℝ ω b := by
    simp [inner_add_right, hω]
  have ha₁ := (abs_le.mp ha).1
  have hu : 0 < ‖ω + b‖ ^ 2 := by nlinarith [sq_nonneg ‖b‖]
  have hm₀ : 0 ≤ inner ℝ ω (ω + b) := by linarith
  have hsmall : ‖ω + b‖ ^ 2 ≤ 2 * inner ℝ ω (ω + b) := by
    nlinarith [norm_nonneg b]
  simpa only [add_sub_cancel_left] using
    residual_nonneg_of_norm_sq_le_two_inner ω (ω + b) v w hω hv hωv huw hu hm₀ hsmall hw

theorem shrinking_sphere_residual_nonneg_of_norm (ω b v w : E)
    (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1) (hωv : inner ℝ ω v = 0)
    (hb : ‖b‖ ≤ 1 / 4) (huw : inner ℝ (ω + b) w = 0)
    (hw : ‖w‖ = 1 / ‖ω + b‖) :
    0 ≤ ‖perpendicularComponent ω (ω - (1 / ‖ω + b‖ ^ 2) • (ω + b))‖ ^ 2 +
      ‖perpendicularComponent ω (v - w)‖ ^ 2 -
      (inner ℝ b ((1 / ‖ω + b‖ ^ 2) • (ω + b))) ^ 2 -
      (inner ℝ b w) ^ 2 := by
  apply shrinking_sphere_residual_nonneg ω b v w hω hv hωv hb huw
  rw [hw, div_pow, one_pow]

theorem shrinking_sphere_hessian_lower_bound (ω b v w : E)
    (H : E → E → ℝ) (r c β : ℝ)
    (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1) (hωv : inner ℝ ω v = 0)
    (hb : ‖b‖ ≤ 1 / 4) (huw : inner ℝ (ω + b) w = 0)
    (hw : ‖w‖ ^ 2 = 1 / ‖ω + b‖ ^ 2)
    (hc : 0 ≤ c) (hβ : 0 ≤ β)
    (hH : ∀ x, H x x ≤ -(c * β) * ‖x‖ ^ 2) :
    (32 / 25) * c * r ^ 2 * β ≤
      ‖perpendicularComponent ω (ω - (1 / ‖ω + b‖ ^ 2) • (ω + b))‖ ^ 2 +
      ‖perpendicularComponent ω (v - w)‖ ^ 2 -
      (inner ℝ b ((1 / ‖ω + b‖ ^ 2) • (ω + b))) ^ 2 -
      (inner ℝ b w) ^ 2 -
      r ^ 2 * (H ((1 / ‖ω + b‖ ^ 2) • (ω + b))
        ((1 / ‖ω + b‖ ^ 2) • (ω + b)) + H w w) := by
  have hR := shrinking_sphere_residual_nonneg ω b v w hω hv hωv hb huw hw
  have hlow : 3 / 4 ≤ ‖ω + b‖ := by
    have ht := norm_add_le (ω + b) (-b)
    simp only [add_neg_cancel_right, norm_neg, hω] at ht
    linarith
  have hn0 : ‖ω + b‖ ≠ 0 := by linarith
  have hD : 0 < ‖ω + b‖ ^ 2 := sq_pos_of_ne_zero hn0
  have hup : ‖ω + b‖ ^ 2 ≤ 25 / 16 := by
    have ht := norm_add_le ω b
    rw [hω] at ht
    nlinarith [norm_nonneg (ω + b)]
  have hq : ‖(1 / ‖ω + b‖ ^ 2) • (ω + b)‖ ^ 2 = 1 / ‖ω + b‖ ^ 2 := by
    rw [norm_smul_sq]
    field_simp [hn0]
  have hqH := hH ((1 / ‖ω + b‖ ^ 2) • (ω + b))
  have hwH := hH w
  rw [hq] at hqH
  rw [hw] at hwH
  have hratio : 32 / 25 ≤ 2 / ‖ω + b‖ ^ 2 := by
    apply (le_div_iff₀ hD).2
    linarith
  have hcoeff : 0 ≤ c * r ^ 2 * β := by positivity
  have hratio' := mul_le_mul_of_nonneg_right hratio hcoeff
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hqH hwH) (sq_nonneg r)
  have hbound : (32 / 25) * c * r ^ 2 * β ≤
      -(r ^ 2 * (H ((1 / ‖ω + b‖ ^ 2) • (ω + b))
        ((1 / ‖ω + b‖ ^ 2) • (ω + b)) + H w w)) := by
    calc
      (32 / 25) * c * r ^ 2 * β = (32 / 25) * (c * r ^ 2 * β) := by ring
      _ ≤ 2 / ‖ω + b‖ ^ 2 * (c * r ^ 2 * β) := hratio'
      _ = -(r ^ 2 * (-(c * β) * (1 / ‖ω + b‖ ^ 2) +
          -(c * β) * (1 / ‖ω + b‖ ^ 2))) := by ring
      _ ≤ _ := neg_le_neg hsum
  linarith only [hR, hbound]

theorem absorb_shrinking_sphere_errors
    (S A r β ε C₀ C₁ C₂ C₃ : ℝ)
    (hr : 0 < r) (hβ : 0 < β) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (_hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hsmall : r * β ^ 2 ≤ ε)
    (hbackground : 4 * (C₀ + C₃) ≤ A * β)
    (hperturbation : (C₁ + C₂) * ε ≤ A / 4)
    (hS : A * r ^ 2 * β - C₀ * r ^ 2 - C₁ * r ^ 3 * β ^ 3 -
      C₂ * ε * r ^ 2 * β - C₃ * ε ^ 2 * r ^ 2 ≤ S) :
    A / 2 * r ^ 2 * β ≤ S := by
  have hscale : 0 ≤ r ^ 2 * β := by positivity
  have hcubic : r ^ 3 * β ^ 3 ≤ ε * r ^ 2 * β := by
    calc
      r ^ 3 * β ^ 3 = (r * β ^ 2) * (r ^ 2 * β) := by ring
      _ ≤ ε * (r ^ 2 * β) := mul_le_mul_of_nonneg_right hsmall hscale
      _ = ε * r ^ 2 * β := by ring
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have h₀ := mul_le_mul_of_nonneg_right hbackground (sq_nonneg r)
  have h₁ := mul_le_mul_of_nonneg_left hcubic hC₁
  have h₂ := mul_le_mul_of_nonneg_right hperturbation hscale
  have h₃ := mul_le_mul_of_nonneg_right hεsq
    (mul_nonneg hC₃ (sq_nonneg r))
  nlinarith

theorem radius_gradient_small_of_radius_profile_small
    (r β ε : ℝ) (hr : 0 ≤ r) (hβ : 1 ≤ β)
    (hsmall : r * β ^ 2 ≤ ε) (hε : ε ≤ 1 / 4) : r * β ≤ 1 / 4 := by
  have hβ' : 0 ≤ β := by linarith
  have hs : β ≤ β ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hs hr
  linarith

theorem shrinking_sphere_expression_pos
    (S A r β ε C₀ C₁ C₂ C₃ : ℝ)
    (hA : 0 < A) (hr : 0 < r) (hβ : 0 < β) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hsmall : r * β ^ 2 ≤ ε)
    (hbackground : 4 * (C₀ + C₃) ≤ A * β)
    (hperturbation : (C₁ + C₂) * ε ≤ A / 4)
    (hS : A * r ^ 2 * β - C₀ * r ^ 2 - C₁ * r ^ 3 * β ^ 3 -
      C₂ * ε * r ^ 2 * β - C₃ * ε ^ 2 * r ^ 2 ≤ S) : 0 < S := by
  have hlower := absorb_shrinking_sphere_errors S A r β ε C₀ C₁ C₂ C₃
    hr hβ hε₀ hε₁ hC₀ hC₁ hC₂ hC₃ hsmall hbackground hperturbation hS
  have hpos : 0 < A / 2 * r ^ 2 * β := by positivity
  exact lt_of_lt_of_le hpos hlower

#print axioms shrinking_sphere_residual_nonneg
#print axioms shrinking_sphere_residual_nonneg_of_norm
#print axioms shrinking_sphere_hessian_lower_bound
#print axioms absorb_shrinking_sphere_errors
#print axioms shrinking_sphere_expression_pos

end OAI.AnisotropicCalderon.ShrinkingGeometry
