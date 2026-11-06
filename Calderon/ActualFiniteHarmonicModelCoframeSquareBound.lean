import Calderon.ActualFiniteHarmonicModelSourceEnergy

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic

lemma norm_coframe_sum_sub_sq_le
    (c : Fin 3 → ℝ) (X Y : Fin 3 → SphereL2) (J s : ℝ)
    (hJ : 0 ≤ J) (hs : 0 ≤ s) (hc : ∀ a, |c a| ≤ J) (hY : ∀ a, ‖Y a‖ ≤ J*s) :
    ‖∑ a : Fin 3, c a • (X a-Y a)‖^2 ≤
      6*J^2*(∑ a : Fin 3, ‖X a‖^2)+18*J^4*s^2 := by
  let S := ∑ a : Fin 3, ‖X a‖
  let Q := ∑ a : Fin 3, ‖X a‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hterm (a : Fin 3) : ‖c a • (X a-Y a)‖ ≤ J*(‖X a‖+J*s) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hc a) ((norm_sub_le _ _).trans (add_le_add_right (hY a) _)) (norm_nonneg _) hJ
  have hn : ‖∑ a : Fin 3, c a • (X a-Y a)‖ ≤ J*(S+3*J*s) := by
    calc
      _ ≤ ∑ a : Fin 3, ‖c a • (X a-Y a)‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin 3, J*(‖X a‖+J*s) := Finset.sum_le_sum (fun a _ => hterm a)
      _ = _ := by dsimp only [S]; simp only [Fin.sum_univ_three]; ring
  have hSQ : S^2 ≤ 3*Q := by
    dsimp only [S,Q]
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖X 0‖-‖X 1‖),sq_nonneg (‖X 0‖-‖X 2‖),sq_nonneg (‖X 1‖-‖X 2‖)]
  have hsum : (S+3*J*s)^2 ≤ 6*Q+18*J^2*s^2 := by
    nlinarith [sq_nonneg (S-3*J*s)]
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    _ ≤ (J*(S+3*J*s))^2 := hn2
    _ = J^2*(S+3*J*s)^2 := by ring
    _ ≤ J^2*(6*Q+18*J^2*s^2) := mul_le_mul_of_nonneg_left hsum (sq_nonneg J)
    _ = _ := by dsimp only [Q]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
