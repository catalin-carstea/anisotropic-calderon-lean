import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- Equal-norm orthogonal pairs give the exact two-component Bessel bound at a unit vector. -/
theorem unit_orthogonal_equal_norm_bessel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega q w : E) (homega : ‖omega‖ = 1) (hq : q ≠ 0)
    (hqw : ⟪q,w⟫_ℝ = 0) (hww : ‖w‖^2 = ‖q‖^2) :
    ⟪omega,q⟫_ℝ^2+⟪omega,w⟫_ℝ^2 ≤ ‖q‖^2 := by
  let c := ‖q‖^2
  let a := ⟪omega,q⟫_ℝ
  let d := ⟪omega,w⟫_ℝ
  have hc : 0 < c := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hoo : ⟪omega,omega⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,homega]; norm_num
  have hqq : ⟪q,q⟫_ℝ = c := real_inner_self_eq_norm_sq q
  have hww' : ⟪w,w⟫_ℝ = c := (real_inner_self_eq_norm_sq _).trans hww
  have hqo : ⟪q,omega⟫_ℝ = a := real_inner_comm _ _
  have hwo : ⟪w,omega⟫_ℝ = d := real_inner_comm _ _
  have hwq : ⟪w,q⟫_ℝ = 0 := (real_inner_comm _ _).trans hqw
  have he : ⟪c • omega-a • q-d • w,c • omega-a • q-d • w⟫_ℝ =
      c^2-c*(a^2+d^2) := by
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      hoo,hqq,hww',hqo,hwo,hqw,hwq]
    dsimp only [a,d]
    ring
  have hn : 0 ≤ c^2-c*(a^2+d^2) :=
    he ▸ (real_inner_self_nonneg (x := c • omega-a • q-d • w))
  have hmul : (a^2+d^2)*c ≤ c*c := by nlinarith
  exact (mul_le_mul_iff_left₀ hc).mp hmul

/-- Unit speed perturbations have an exact half bound for the normalized second normal. -/
theorem half_le_inner_normalized_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega b : E) (homega : ‖omega‖ = 1) (hb : ‖b‖ ≤ 1) (hn : omega+b ≠ 0) :
    (1/2 : ℝ) ≤ ⟪omega,(‖omega+b‖^2)⁻¹ • (omega+b)⟫_ℝ := by
  have hC : 0 < ‖omega+b‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hoo : ⟪omega,omega⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,homega]; norm_num
  have hb2 : ‖b‖^2 ≤ 1 := by nlinarith [norm_nonneg b]
  have hsum : ‖omega+b‖^2 ≤ 2*⟪omega,omega+b⟫_ℝ := by
    rw [norm_add_sq_real,homega,inner_add_right,hoo]
    nlinarith
  rw [real_inner_smul_right]
  have heq : (‖omega+b‖^2)⁻¹*⟪omega,omega+b⟫_ℝ =
      ⟪omega,omega+b⟫_ℝ/‖omega+b‖^2 := by ring
  rw [heq]
  exact (le_div_iff₀ hC).mpr (by nlinarith)

/-- The exact Euclidean moving-sphere leading form is nonnegative for a small radius gradient. -/
theorem moving_sphere_leading_form_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega v b q w : E) (homega : ‖omega‖ = 1) (hv : ‖v‖ = 1)
    (hov : ⟪omega,v⟫_ℝ = 0) (hb : ‖b‖ ≤ 1) (hn : omega+b ≠ 0)
    (hq : q = (‖omega+b‖^2)⁻¹ • (omega+b))
    (hnw : ⟪omega+b,w⟫_ℝ = 0) (hww : ‖w‖^2 = ‖q‖^2) :
    0 ≤ ‖omega-q‖^2+‖v-w‖^2-2*(⟪b,q⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
  have hC : 0 < ‖omega+b‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hnq : ⟪omega+b,q⟫_ℝ = 1 := by
    rw [hq,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ hC.ne'
  have hqne : q ≠ 0 := by
    intro h
    have hh : (0 : ℝ) = 1 := by simpa only [h,inner_zero_right] using hnq
    norm_num at hh
  have hqw : ⟪q,w⟫_ℝ = 0 := by rw [hq,real_inner_smul_left,hnw,mul_zero]
  let a := ⟪omega,q⟫_ℝ
  let d := ⟪omega,w⟫_ℝ
  let z := ‖w-d • omega‖
  have ha : (1/2 : ℝ) ≤ a := by
    dsimp only [a]
    rw [hq]
    exact half_le_inner_normalized_sum omega b homega hb hn
  have hB := unit_orthogonal_equal_norm_bessel omega q w homega hqne hqw hww
  have hwo : ⟪w,omega⟫_ℝ = d := real_inner_comm _ _
  have hvo : ⟪v,omega⟫_ℝ = 0 := (real_inner_comm _ _).trans hov
  have hzsq : z^2 = ‖q‖^2-d^2 := by
    dsimp only [z]
    rw [norm_sub_sq_real,real_inner_smul_right,hwo,norm_smul,Real.norm_eq_abs,
      homega,mul_one,sq_abs,hww]
    ring
  have ha0 : 0 ≤ a := by linarith
  have hz0 : 0 ≤ z := norm_nonneg _
  have haz : a ≤ z := (sq_le_sq₀ ha0 hz0).mp (by
    change a^2+d^2 ≤ ‖q‖^2 at hB
    nlinarith)
  have hvw : ⟪v,w⟫_ℝ ≤ z := by
    have hh := real_inner_le_norm v (w-d • omega)
    rw [inner_sub_right,real_inner_smul_right,hvo,mul_zero,sub_zero,hv,one_mul] at hh
    exact hh
  have hbq : ⟪b,q⟫_ℝ = 1-a := by
    rw [inner_add_left] at hnq
    change a+⟪b,q⟫_ℝ = 1 at hnq
    linarith
  have hbw : ⟪b,w⟫_ℝ = -d := by
    rw [inner_add_left] at hnw
    change d+⟪b,w⟫_ℝ = 0 at hnw
    linarith
  have hproduct : 0 ≤ (z-a)*(z+a-1) :=
    mul_nonneg (sub_nonneg.mpr haz) (by linarith)
  rw [norm_sub_sq_real,norm_sub_sq_real,homega,hv,hww,hbq,hbw]
  change 0 ≤ 1^2-2*a+‖q‖^2+(1^2-2*⟪v,w⟫_ℝ+‖q‖^2)-2*((1-a)^2+(-d)^2)
  nlinarith [hproduct,hvw,hzsq]

/-- An exact quadratic bound for the angular term in the small-gradient tube/sphere regime. -/
theorem moving_sphere_angular_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega v b q w : E) (homega : ‖omega‖ = 1) (hv : ‖v‖ = 1)
    (hov : ⟪omega,v⟫_ℝ = 0) (hb : ‖b‖ ≤ 1) (hn : omega+b ≠ 0)
    (hq : q = (‖omega+b‖^2)⁻¹ • (omega+b))
    (hnw : ⟪omega+b,w⟫_ℝ = 0) (hww : ‖w‖^2 = ‖q‖^2) :
    ‖b‖^2/8 ≤ ‖q-⟪omega,q⟫_ℝ • omega‖^2+
      ‖v-w+⟪omega,w⟫_ℝ • omega‖^2 := by
  let c0 := ‖omega+b‖^2
  let C := ‖q‖^2
  let a := ⟪omega,q⟫_ℝ
  let d := ⟪omega,w⟫_ℝ
  let A := ‖q-a • omega‖^2+‖v-w+d • omega‖^2
  have hc0 : 0 < c0 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hnq : ⟪omega+b,q⟫_ℝ = 1 := by
    rw [hq,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ hc0.ne'
  have hscale : c0 • q = omega+b := by
    rw [hq,smul_smul,mul_inv_cancel₀ hc0.ne',one_smul]
  have hCC : c0*C = 1 := by
    have hh : ⟪c0 • q,q⟫_ℝ = 1 := by rw [hscale]; exact hnq
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_sq,C] using hh
  have hAC : c0*a = ⟪omega,omega+b⟫_ℝ := by
    calc c0*a = ⟪omega,c0 • q⟫_ℝ := by simp only [real_inner_smul_right,a]
      _ = ⟪omega,omega+b⟫_ℝ := by rw [hscale]
  have hoo : ⟪omega,omega⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,homega]; norm_num
  have hNorm : c0 = 1+2*⟪omega,b⟫_ℝ+‖b‖^2 := by
    dsimp only [c0]
    rw [norm_add_sq_real,homega]
    norm_num
  have hinner : ⟪omega,omega+b⟫_ℝ = 1+⟪omega,b⟫_ℝ := by rw [inner_add_right,hoo]
  have hDiff : ‖omega-q‖^2 = 1-2*a+C := by
    rw [norm_sub_sq_real,homega]
    norm_num [a,C]
  have hInv : ‖omega-q‖^2*c0 = ‖b‖^2 := by
    rw [hDiff]
    nlinarith [hCC,hAC,hNorm,hinner]
  have hqo : ⟪q,omega⟫_ℝ = a := real_inner_comm _ _
  have hwo : ⟪w,omega⟫_ℝ = d := real_inner_comm _ _
  have hvo : ⟪v,omega⟫_ℝ = 0 := (real_inner_comm _ _).trans hov
  have hReal : ‖q-a • omega‖^2 = C-a^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,hqo,norm_smul,Real.norm_eq_abs,
      homega,mul_one,sq_abs]
    dsimp only [C]
    ring
  have hImag : ‖v-w+d • omega‖^2 = ‖v-w‖^2-d^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,inner_sub_left,hvo,hwo,
      norm_smul,Real.norm_eq_abs,homega,mul_one,sq_abs]
    ring
  have hAexpr : A = C-a^2+‖v-w‖^2-d^2 := by dsimp only [A]; rw [hReal,hImag]; ring
  have hbq : ⟪b,q⟫_ℝ = 1-a := by
    rw [inner_add_left] at hnq
    change a+⟪b,q⟫_ℝ = 1 at hnq
    linarith
  have hbw : ⟪b,w⟫_ℝ = -d := by
    rw [inner_add_left] at hnw
    change d+⟪b,w⟫_ℝ = 0 at hnw
    linarith
  have hE := moving_sphere_leading_form_nonneg omega v b q w homega hv hov hb hn hq hnw hww
  rw [hbq,hbw] at hE
  have hA2 : ‖omega-q‖^2 ≤ 2*A := by
    have hI : 0 ≤ ‖v-w+d • omega‖^2 := sq_nonneg _
    nlinarith [hAexpr,hImag,hDiff,hE]
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcUpper : c0 ≤ 4 := by
    have hh := norm_add_le omega b
    rw [homega] at hh
    dsimp only [c0]
    have hle : ‖omega+b‖ ≤ 2 := by linarith
    simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
      (sq_le_sq₀ (norm_nonneg (omega+b)) (by norm_num : (0 : ℝ) ≤ 2)).mpr hle
  have hm := mul_le_mul_of_nonneg_right hA2 hc0.le
  have hu := mul_le_mul_of_nonneg_left hcUpper (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA0)
  change ‖b‖^2/8 ≤ A
  nlinarith [hInv,hm,hu]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
