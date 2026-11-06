import Calderon.MixedKernelConstruction.MixedKernelMovingSphereStability
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- An ACTUAL right inverse of a small operator perturbation has the needed inverse error bound. -/
theorem inverse_operator_near_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) (eta : ℝ) (heta : eta ≤ 1/2)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta) (hTR : ∀ u : E, T (R u) = u) :
    ‖R‖ ≤ 2 ∧ ‖R-ContinuousLinearMap.id ℝ E‖ ≤ 2*eta := by
  have heta0 : 0 ≤ eta := (norm_nonneg _).trans hT
  have hdiff (u : E) : ‖R u-u‖ ≤ eta*‖R u‖ := by
    have hh := (T-ContinuousLinearMap.id ℝ E).le_opNorm (R u)
    have hh' : ‖u-R u‖ ≤ ‖T-ContinuousLinearMap.id ℝ E‖*‖R u‖ := by
      simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,hTR] using hh
    rw [norm_sub_rev] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hRpoint (u : E) : ‖R u‖ ≤ 2*‖u‖ := by
    have hh := norm_sub_le (R u) u
    have htriangle : ‖R u‖ ≤ ‖u‖+‖R u-u‖ := by
      calc ‖R u‖ = ‖u+(R u-u)‖ := by congr 1; abel
        _ ≤ ‖u‖+‖R u-u‖ := norm_add_le _ _
    have hm := mul_le_mul_of_nonneg_right heta (norm_nonneg (R u))
    nlinarith [hdiff u]
  refine ⟨R.opNorm_le_bound (by norm_num) hRpoint,?_⟩
  apply (R-ContinuousLinearMap.id ℝ E).opNorm_le_bound (by positivity)
  intro u
  change ‖R u-u‖ ≤ (2*eta)*‖u‖
  have hh := mul_le_mul_of_nonneg_left (hRpoint u) heta0
  nlinarith [hdiff u]

/-- Literal normalized metric normals are O(eta) close to their Euclidean comparisons. -/
theorem normalized_operator_vector_near_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (n : E) (eta : ℝ) (heta : eta ≤ 1/2)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta)
    (hn0 : (1/2 : ℝ) ≤ ‖n‖) (hn1 : ‖n‖ ≤ 2) :
    (1/8 : ℝ) ≤ ⟪n,T n⟫_ℝ ∧
    ‖(⟪n,T n⟫_ℝ)⁻¹ • T n-(‖n‖^2)⁻¹ • n‖ ≤ 32*eta := by
  let a := ⟪n,T n⟫_ℝ
  let N := ‖n‖^2
  have heta0 : 0 ≤ eta := (norm_nonneg _).trans hT
  have hnpos : 0 < ‖n‖ := by linarith
  have hN : (1/4 : ℝ) ≤ N := by
    have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1/2) (norm_nonneg n)).mpr hn0
    simpa only [show (1/2 : ℝ)^2 = 1/4 by norm_num] using hh
  have hNpos : 0 < N := by linarith
  have hdiff : ‖T n-n‖ ≤ eta*‖n‖ := by
    have hh := (T-ContinuousLinearMap.id ℝ E).le_opNorm n
    exact hh.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg n))
  have hinner : |a-N| ≤ eta*N := by
    have he : a-N = ⟪n,T n-n⟫_ℝ := by
      dsimp only [a,N]
      rw [inner_sub_right,real_inner_self_eq_norm_sq]
    rw [he]
    calc |⟪n,T n-n⟫_ℝ| ≤ ‖n‖*‖T n-n‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖n‖*(eta*‖n‖) := mul_le_mul_of_nonneg_left hdiff (norm_nonneg n)
      _ = eta*N := by dsimp only [N]; ring
  have ha : (1/8 : ℝ) ≤ a := by
    have hh := (abs_le.mp hinner).1
    have hm := mul_le_mul_of_nonneg_right heta hNpos.le
    nlinarith
  have hapos : 0 < a := by linarith
  have hai : a⁻¹ ≤ 8 := by rw [inv_eq_one_div]; exact (div_le_iff₀ hapos).mpr (by linarith)
  have hdiff2 : ‖T n-n‖ ≤ 2*eta :=
    hdiff.trans (by nlinarith [mul_le_mul_of_nonneg_left hn1 heta0])
  have hInvIdentity : |a⁻¹-N⁻¹| = |a-N|/(a*N) := by
    have he : a⁻¹-N⁻¹ = -(a-N)/(a*N) := by field_simp [hapos.ne',hNpos.ne'] <;> ring
    rw [he,abs_div,abs_neg,abs_of_pos (mul_pos hapos hNpos)]
  have hinvdiff : |a⁻¹-N⁻¹| ≤ 8*eta := by
    rw [hInvIdentity]
    apply (div_le_iff₀ (mul_pos hapos hNpos)).mpr
    have hm : eta*N ≤ (8*eta)*(a*N) := by
      have hh := mul_le_mul_of_nonneg_left ha (mul_nonneg heta0 hNpos.le)
      nlinarith
    exact hinner.trans hm
  have hvec : a⁻¹ • T n-N⁻¹ • n = a⁻¹ • (T n-n)+(a⁻¹-N⁻¹) • n := by
    rw [smul_sub,sub_smul]
    abel
  refine ⟨ha,?_⟩
  change ‖a⁻¹ • T n-N⁻¹ • n‖ ≤ 32*eta
  rw [hvec]
  calc ‖a⁻¹ • (T n-n)+(a⁻¹-N⁻¹) • n‖ ≤
        ‖a⁻¹ • (T n-n)‖+‖(a⁻¹-N⁻¹) • n‖ := norm_add_le _ _
    _ = a⁻¹*‖T n-n‖+|a⁻¹-N⁻¹| * ‖n‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hapos)]
    _ ≤ 8*(2*eta)+(8*eta)*2 := by
      exact add_le_add (mul_le_mul hai hdiff2 (norm_nonneg _) (by norm_num))
        (mul_le_mul hinvdiff hn1 (norm_nonneg n) (by positivity))
    _ = 32*eta := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
