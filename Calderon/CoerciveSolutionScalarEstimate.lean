import Calderon.ParametricCoerciveInverse
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_solution_sub_le_of_scalar_coercivity
    (B C : V →L[ℝ] StrongDual ℝ V) (c : ℝ) (hc : 0 < c)
    (hC : ∀ v : V, c * ‖v‖^2 ≤ C v v) (hBC : ‖B-C‖ ≤ c/2)
    (ell ell0 : StrongDual ℝ V) (z z0 : V)
    (hz : ∀ v : V, B z v = ell v) (hz0 : ∀ v : V, C z0 v = ell0 v) :
    ‖z-z0‖ ≤ (2/c)*(‖ell-ell0‖+‖B-C‖*‖z0‖) := by
  let d : V := z-z0
  have hDiff : |(B-C) d d| ≤ ‖B-C‖ * ‖d‖ * ‖d‖ := by
    have h := ((B-C) d).le_opNorm d
    have h' := mul_le_mul_of_nonneg_right ((B-C).le_opNorm d) (norm_nonneg d)
    exact h.trans h'
  have hDiffSmall : |(B-C) d d| ≤ (c/2)*‖d‖^2 := by
    have h := mul_le_mul_of_nonneg_right hBC (sq_nonneg ‖d‖)
    exact hDiff.trans (by simpa only [pow_two,mul_assoc] using h)
  have hLower : (c/2)*‖d‖^2 ≤ B d d := by
    have hScalar : (B-C) d d = B d d-C d d := by simp only [ContinuousLinearMap.sub_apply]
    have hAbs := neg_abs_le ((B-C) d d)
    have hReference := hC d
    rw [hScalar] at hAbs hDiffSmall
    linarith
  have hResidual : B d d = (ell-ell0) d + (C-B) z0 d := by
    dsimp only [d]
    simp only [map_sub,ContinuousLinearMap.sub_apply,hz,hz0]
    ring
  have hEll : (ell-ell0) d ≤ ‖ell-ell0‖*‖d‖ :=
    (le_abs_self _).trans ((ell-ell0).le_opNorm d)
  have hOp : (C-B) z0 d ≤ (‖B-C‖*‖z0‖)*‖d‖ := by
    have h := ((C-B) z0).le_opNorm d
    have h' := mul_le_mul_of_nonneg_right ((C-B).le_opNorm z0) (norm_nonneg d)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,norm_sub_rev] using h.trans h')
  have hUpper : B d d ≤ (‖ell-ell0‖+‖B-C‖*‖z0‖)*‖d‖ := by
    rw [hResidual]
    nlinarith
  have hcHalf : 0 < c/2 := by linarith
  by_cases hd : d = 0
  · change ‖d‖ ≤ _
    rw [hd,norm_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hc.le)
      (add_nonneg (ell-ell0).opNorm_nonneg (mul_nonneg (B-C).opNorm_nonneg (norm_nonneg z0)))
  · have hdNorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hProduct : (c/2*‖d‖)*‖d‖ ≤ (‖ell-ell0‖+‖B-C‖*‖z0‖)*‖d‖ := by
      simpa only [pow_two,mul_assoc] using hLower.trans hUpper
    have hCancel := (mul_le_mul_iff_left₀ hdNorm).mp hProduct
    have hDiv : ‖d‖ ≤ (‖ell-ell0‖+‖B-C‖*‖z0‖)/(c/2) :=
      (le_div_iff₀ hcHalf).mpr (by simpa only [mul_comm] using hCancel)
    have hRewrite : (‖ell-ell0‖+‖B-C‖*‖z0‖)/(c/2) =
        (2/c)*(‖ell-ell0‖+‖B-C‖*‖z0‖) := by
      field_simp [hc.ne'] <;> ring
    exact hDiv.trans_eq hRewrite

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.norm_solution_sub_le_of_scalar_coercivity
