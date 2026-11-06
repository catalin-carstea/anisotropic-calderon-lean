import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Presealed elementary real-Hilbert finite-sum and scalar integral bounds.
No geometric/domain/error estimate premise is introduced. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.ScalarHilbertFormBounds

theorem abs_real_inner_neg_triple_sum_smul_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : Fin 3 → Fin 3 → Fin 3 → ℝ) (v : Fin 3 → E) (u z : E) (A N : ℝ)
    (hA : 0 ≤ A) (hc : ∀ i j a : Fin 3, |c i j a| ≤ A)
    (hv : ∀ a : Fin 3, ‖v a‖ ≤ 2*‖z‖) (hu : ‖u‖ ≤ ‖z‖) (hN : ‖z‖^2 ≤ N) :
    |⟪-(∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, (c i j a) • v a),u⟫_ℝ| ≤
      54*A*N := by
  have hInner (a : Fin 3) : |⟪v a,u⟫_ℝ| ≤ 2*N := by
    calc
      _ ≤ ‖v a‖*‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (2*‖z‖)*‖z‖ := mul_le_mul (hv a) hu (norm_nonneg _) (by positivity)
      _ = 2*‖z‖^2 := by ring
      _ ≤ 2*N := mul_le_mul_of_nonneg_left hN (by norm_num)
  have hTerm (i j a : Fin 3) : |(c i j a)*⟪v a,u⟫_ℝ| ≤ A*(2*N) := by
    rw [abs_mul]
    exact mul_le_mul (hc i j a) (hInner a) (abs_nonneg _) hA
  have hSum : |∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, (c i j a)*⟪v a,u⟫_ℝ| ≤ 54*A*N := by
    calc
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, ∑ a : Fin 3, (c i j a)*⟪v a,u⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |∑ a : Fin 3, (c i j a)*⟪v a,u⟫_ℝ| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, |(c i j a)*⟪v a,u⟫_ℝ| :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, A*(2*N) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
          (fun a _ => hTerm i j a)))
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  simpa only [inner_neg_left,sum_inner,real_inner_smul_left,abs_neg] using hSum

theorem abs_integral_le_const_mul_integral
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f w : X → ℝ) (C : ℝ)
    (hf : Integrable f μ) (hw : Integrable w μ) (hPoint : ∀ x : X, |f x| ≤ C*w x) :
    |∫ x, f x ∂μ| ≤ C*(∫ x, w x ∂μ) := by
  calc
    _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C*w x ∂μ := integral_mono hf.abs (hw.const_mul C) hPoint
    _ = _ := integral_const_mul C w

end OAI.AnisotropicCalderon.ScalarHilbertFormBounds
