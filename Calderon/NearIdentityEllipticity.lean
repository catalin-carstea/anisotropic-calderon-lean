import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_lower_bound_of_norm_sub_id_le_half (H : E →L[ℝ] E)
    (hH : ‖H-ContinuousLinearMap.id ℝ E‖ ≤ (1/2 : ℝ)) (u : E) :
    (1/2 : ℝ)*‖u‖^2 ≤ inner ℝ (H u) u := by
  have hd : |inner ℝ ((H-ContinuousLinearMap.id ℝ E) u) u| ≤ (1/2 : ℝ)*‖u‖^2 := by
    calc
      _ ≤ ‖(H-ContinuousLinearMap.id ℝ E) u‖*‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H-ContinuousLinearMap.id ℝ E‖*‖u‖)*‖u‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (1/2 : ℝ)*‖u‖^2 := by nlinarith [sq_nonneg ‖u‖]
  have he : inner ℝ ((H-ContinuousLinearMap.id ℝ E) u) u = inner ℝ (H u) u-‖u‖^2 := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,inner_sub_left,
      real_inner_self_eq_norm_sq]
  have hl := neg_le_of_abs_le hd
  rw [he] at hl
  linarith

theorem inner_upper_bound_of_norm_sub_id_le_half (H : E →L[ℝ] E)
    (hH : ‖H-ContinuousLinearMap.id ℝ E‖ ≤ (1/2 : ℝ)) (u v : E) :
    |inner ℝ (H u) v| ≤ (3/2 : ℝ)*‖u‖*‖v‖ := by
  have hn : ‖H‖ ≤ (3/2 : ℝ) := by
    have ht := norm_add_le (H-ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
    rw [sub_add_cancel] at ht
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
    linarith
  calc
    _ ≤ ‖H u‖*‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖H‖*‖u‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (3/2 : ℝ)*‖u‖*‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (norm_nonneg _)

theorem exists_common_radius_quadratic_le_half (epsilon B : ℝ)
    (he : 0 < epsilon) (hB : 0 ≤ B) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ epsilon ∧
      ∀ r : ℝ, |r| ≤ delta → B*r^2 ≤ (1/2 : ℝ) := by
  let delta := min epsilon (min 1 (1/(2*(B+1))))
  have hb : 0 < 2*(B+1) := by positivity
  have hd : 0 < delta := lt_min he (lt_min (by norm_num) (by positivity))
  refine ⟨delta,hd,min_le_left _ _,?_⟩
  intro r hr
  have hr1 : |r| ≤ 1 := hr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrb : |r| ≤ 1/(2*(B+1)) :=
    hr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr2 : r^2 ≤ |r| := by
    have hm := mul_le_mul_of_nonneg_left hr1 (abs_nonneg r)
    nlinarith [sq_abs r]
  have hden := (le_div_iff₀ hb).mp hrb
  nlinarith [abs_nonneg r,mul_le_mul_of_nonneg_left hr2 hB]
end OAI.AnisotropicCalderon.ConnectionError
