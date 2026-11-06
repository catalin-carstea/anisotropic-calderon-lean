import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_deriv_le_of_second_deriv_le (f : ℝ → V) (hf : ContDiff ℝ ∞ f)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hzero : HasDerivAt f 0 0)
    (hbound : ∀ t : ℝ, |t| ≤ δ → ‖deriv (deriv f) t‖ ≤ B)
    (t : ℝ) (ht : |t| ≤ δ) : ‖deriv f t‖ ≤ B * |t| := by
  have hDF : ContDiff ℝ ∞ (deriv f) := by
    apply ContDiff.deriv'
    simpa using hf
  have h0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ⟩
  have ht' : t ∈ Icc (-δ) δ := abs_le.mp ht
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Icc (-δ) δ) => hDF.differentiable (by simp) x)
    (fun x hx => hbound x (abs_le.mpr hx)) (convex_Icc (-δ) δ) h0 ht'
  simpa only [hzero.deriv,sub_zero,Real.norm_eq_abs] using h

theorem norm_sub_le_quadratic_of_second_deriv_le (f : ℝ → V) (hf : ContDiff ℝ ∞ f)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hzero : HasDerivAt f 0 0)
    (hbound : ∀ t : ℝ, |t| ≤ δ → ‖deriv (deriv f) t‖ ≤ B)
    (r : ℝ) (hr : |r| ≤ δ) : ‖f r - f 0‖ ≤ B * r^2 := by
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) : ‖deriv f t‖ ≤ B * |r| := by
    have ht' : |t| ≤ |r| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
    exact (norm_deriv_le_of_second_deriv_le f hf δ B hδ hB hzero hbound t
      (ht'.trans hr)).trans (mul_le_mul_of_nonneg_left ht' hB)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ uIcc (0 : ℝ) r) => hf.differentiable (by simp) t)
    hd (convex_uIcc (0 : ℝ) r) left_mem_uIcc right_mem_uIcc
  calc
    ‖f r - f 0‖ ≤ (B * |r|) * |r| := by simpa only [sub_zero,Real.norm_eq_abs] using h
    _ = B * r^2 := by rw [mul_assoc,← pow_two,sq_abs]
end OAI.AnisotropicCalderon.ConnectionError
