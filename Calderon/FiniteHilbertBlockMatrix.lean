import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SpectralSylvester

variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]

lemma norm_sq_finite_lp_packet_le (s : Finset ℕ) (a : ∀ k, E k)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) (x : ℕ → ℝ) :
    ‖∑ k ∈ s, lp.single (E := E) 2 k (x k • a k)‖^2 ≤ ∑ k ∈ s, (x k)^2 := by
  have hn := lp.norm_sum_single (E := E) (p := 2)
    (by norm_num : 0 < (2:ℝ≥0∞).toReal) (fun k => x k • a k) s
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hn
  rw [hn]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hsq : ‖a k‖^2 ≤ 1 := by nlinarith [norm_nonneg (a k),ha k hk]
  exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg (x k))).trans_eq (mul_one _)

lemma finite_lp_direction_matrix_pairing
    (T : lp E 2 →L[ℝ] lp E 2) (s : Finset ℕ)
    (a b : ∀ k, E k) (x y : ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, ⟪(T (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i) =
    ⟪T (∑ j ∈ s, lp.single (E := E) 2 j (x j • a j)),
      ∑ i ∈ s, lp.single (E := E) 2 i (y i • b i)⟫_ℝ := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lp.inner_single_right,map_sum]
  simp only [lp.coeFn_sum,Finset.sum_apply]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lp.single_smul,map_smul,lp.coeFn_smul,Pi.smul_apply,
    real_inner_smul_left,real_inner_smul_right]
  ring

lemma finite_lp_direction_matrix_quadratic_bound
    (T : lp E 2 →L[ℝ] lp E 2) (s : Finset ℕ) (a b : ∀ k, E k)
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) (hb : ∀ k ∈ s, ‖b k‖ ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) (hT : ‖T‖ ≤ M) (x y : ℕ → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, ⟪(T (lp.single (E := E) 2 j (a j))) i,b i⟫_ℝ*x j*y i| ≤
      (M/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2) := by
  rw [finite_lp_direction_matrix_pairing]
  let X : lp E 2 := ∑ j ∈ s, lp.single (E := E) 2 j (x j • a j)
  let Y : lp E 2 := ∑ i ∈ s, lp.single (E := E) 2 i (y i • b i)
  have hi : |⟪T X,Y⟫_ℝ| ≤ M*‖X‖*‖Y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (T.le_of_opNorm_le hT X) (norm_nonneg _))
  have hxy : 2*‖X‖*‖Y‖ ≤ ‖X‖^2+‖Y‖^2 := by nlinarith [sq_nonneg (‖X‖-‖Y‖)]
  have hscaled := mul_le_mul_of_nonneg_left hxy hM
  have hx := norm_sq_finite_lp_packet_le s a ha x
  have hy := norm_sq_finite_lp_packet_le s b hb y
  change ‖X‖^2 ≤ _ at hx
  change ‖Y‖^2 ≤ _ at hy
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hx hy) hM
  change |⟪T X,Y⟫_ℝ| ≤ _
  nlinarith

lemma norm_normalize_le_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : F) : ‖NormedSpace.normalize x‖ ≤ 1 := by
  by_cases hx : x=0
  · simp [hx]
  · exact (NormedSpace.norm_normalize hx).le

end OAI.AnisotropicCalderon.SpectralSylvester
