import MixedKernelMetricNormalComparison
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- The exact quadratic form of an operator near the identity has relative error eta. -/
theorem operator_quadratic_error_near_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (x : E) (eta : ℝ)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta) :
    |⟪x,T x⟫_ℝ-‖x‖^2| ≤ eta*‖x‖^2 := by
  have hdiff : ‖T x-x‖ ≤ eta*‖x‖ := by
    have hh := (T-ContinuousLinearMap.id ℝ E).le_opNorm x
    exact hh.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have he : ⟪x,T x⟫_ℝ-‖x‖^2 = ⟪x,T x-x⟫_ℝ := by
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he]
  calc |⟪x,T x-x⟫_ℝ| ≤ ‖x‖*‖T x-x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(eta*‖x‖) := mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
    _ = eta*‖x‖^2 := by ring

/-- A relative quadratic error gives the explicit reciprocal bound needed for normalization. -/
theorem reciprocal_error_of_relative_quadratic_error (a N eta : ℝ)
    (ha : (1/8 : ℝ) ≤ a) (hN : 0 < N) (heta : 0 ≤ eta)
    (herror : |a-N| ≤ eta*N) : |a⁻¹-N⁻¹| ≤ 8*eta := by
  have hapos : 0 < a := by linarith
  have hid : a⁻¹-N⁻¹ = -(a-N)/(a*N) := by field_simp [hapos.ne',hN.ne'] <;> ring
  rw [hid,abs_div,abs_neg,abs_of_pos (mul_pos hapos hN)]
  apply (div_le_iff₀ (mul_pos hapos hN)).mpr
  have hm : eta*N ≤ (8*eta)*(a*N) := by
    have hh := mul_le_mul_of_nonneg_left ha (mul_nonneg heta hN.le)
    nlinarith
  exact herror.trans hm

/-- The ACTUAL inverse-metric characteristic equation controls the imaginary vector length. -/
theorem metric_characteristic_length_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) (n w : E) (eta : ℝ) (heta : eta ≤ 1/4)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta) (hTR : ∀ u : E, T (R u) = u)
    (hn0 : (1/2 : ℝ) ≤ ‖n‖) (hn1 : ‖n‖ ≤ 2)
    (hchar : ⟪w,R w⟫_ℝ = (⟪n,T n⟫_ℝ)⁻¹) :
    ‖w‖^2 ≤ 16 ∧ |‖w‖^2-(‖n‖^2)⁻¹| ≤ 40*eta := by
  have heta0 : 0 ≤ eta := (norm_nonneg _).trans hT
  have heta2 : eta ≤ 1/2 := by linarith
  have ha := (normalized_operator_vector_near_identity T n eta heta2 hT hn0 hn1).1
  have hapos : 0 < ⟪n,T n⟫_ℝ := by linarith
  have hNpos : 0 < ‖n‖^2 := sq_pos_of_pos (by linarith)
  have hci : (⟪n,T n⟫_ℝ)⁻¹ ≤ 8 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hapos).mpr (by linarith)
  have hR := (inverse_operator_near_identity T R eta heta2 hT hTR).2
  have hquadratic := operator_quadratic_error_near_identity R w (2*eta) hR
  rw [hchar,abs_sub_comm] at hquadratic
  have hnorm : ‖w‖^2 ≤ 16 := by
    have hh := (abs_le.mp hquadratic).2
    have hm := mul_le_mul_of_nonneg_right heta (sq_nonneg ‖w‖)
    nlinarith
  have hlength : |‖w‖^2-(⟪n,T n⟫_ℝ)⁻¹| ≤ 32*eta := by
    exact hquadratic.trans (by nlinarith [mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 2*eta)])
  have hrecip := reciprocal_error_of_relative_quadratic_error ⟪n,T n⟫_ℝ (‖n‖^2) eta ha hNpos heta0
    (operator_quadratic_error_near_identity T n eta hT)
  refine ⟨hnorm,?_⟩
  calc |‖w‖^2-(‖n‖^2)⁻¹| =
      |(‖w‖^2-(⟪n,T n⟫_ℝ)⁻¹)+((⟪n,T n⟫_ℝ)⁻¹-(‖n‖^2)⁻¹)| := by congr 1; ring
    _ ≤ |‖w‖^2-(⟪n,T n⟫_ℝ)⁻¹|+|(⟪n,T n⟫_ℝ)⁻¹-(‖n‖^2)⁻¹| := abs_add_le _ _
    _ ≤ 32*eta+8*eta := add_le_add hlength hrecip
    _ = 40*eta := by ring

/-- Actual characteristic vectors have an exact Euclidean orthogonal comparison at linear error. -/
theorem exists_metric_characteristic_comparison
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) (n w : E) (eta : ℝ) (heta : eta ≤ 1/320)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta) (hTR : ∀ u : E, T (R u) = u)
    (hn0 : (1/2 : ℝ) ≤ ‖n‖) (hn1 : ‖n‖ ≤ 2)
    (horth : ⟪n,w⟫_ℝ = 0) (hchar : ⟪w,R w⟫_ℝ = (⟪n,T n⟫_ℝ)⁻¹) :
    ∃ w0 : E, ⟪n,w0⟫_ℝ = 0 ∧ ‖w0‖ = ‖n‖⁻¹ ∧ ‖w-w0‖ ≤ 80*eta := by
  have heta0 : 0 ≤ eta := (norm_nonneg _).trans hT
  have hnpos : 0 < ‖n‖ := by linarith
  have hc : (1/2 : ℝ) ≤ ‖n‖⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hnpos).mpr (by linarith)
  have herr := (metric_characteristic_length_error T R n w eta (by linarith) hT hTR hn0 hn1 hchar).2
  have herr' : |‖w‖^2-(‖n‖⁻¹)^2| ≤ 40*eta := by simpa only [inv_pow] using herr
  obtain ⟨w0,ho,hn,hd⟩ := exists_normalized_orthogonal_near n w (‖n‖⁻¹) (40*eta) hc
    (by positivity) (by linarith) horth herr'
  refine ⟨w0,ho,hn,?_⟩
  linarith

/-- Metric-normalized moving-sphere leading energy retains the required mixed/quadratic error. -/
theorem moving_sphere_metric_normalization_stability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T R : E →L[ℝ] E) (omega v b w : E) (eta : ℝ)
    (homega : ‖omega‖ = 1) (hv : ‖v‖ = 1) (hov : ⟪omega,v⟫_ℝ = 0)
    (hb : ‖b‖ ≤ 1/4) (heta : eta ≤ 1/320)
    (hT : ‖T-ContinuousLinearMap.id ℝ E‖ ≤ eta) (hTR : ∀ u : E, T (R u) = u)
    (horth : ⟪omega+b,w⟫_ℝ = 0)
    (hchar : ⟪w,R w⟫_ℝ = (⟪omega+b,T (omega+b)⟫_ℝ)⁻¹) :
    let q := (⟪omega+b,T (omega+b)⟫_ℝ)⁻¹ • T (omega+b);
    -16*(112*‖b‖*eta+(112*eta)^2) ≤
      ‖omega-q‖^2+‖v-w‖^2-2*(⟪b,q⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
  let n := omega+b
  let q0 := (‖n‖^2)⁻¹ • n
  have heta0 : 0 ≤ eta := (norm_nonneg _).trans hT
  have hn0 : (1/2 : ℝ) ≤ ‖n‖ := by
    have hh := norm_sub_norm_le omega (-b)
    simp only [homega,norm_neg,sub_neg_eq_add] at hh
    change (1/2 : ℝ) ≤ ‖omega+b‖
    linarith
  have hn1 : ‖n‖ ≤ 2 := by
    have hh := norm_add_le omega b
    change ‖omega+b‖ ≤ 2
    rw [homega] at hh
    linarith
  have hnpos : 0 < ‖n‖ := by linarith
  have hn : n ≠ 0 := norm_pos_iff.mp hnpos
  obtain ⟨w0,ho,hw0,hdw⟩ := exists_metric_characteristic_comparison T R n w eta heta hT hTR hn0 hn1 horth hchar
  have hq0norm : ‖q0‖ = ‖n‖⁻¹ := by
    dsimp only [q0]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hnpos))]
    field_simp [hnpos.ne'] <;> ring
  have hqq := (normalized_operator_vector_near_identity T n eta (by linarith) hT hn0 hn1).2
  have hpair : ‖(⟪n,T n⟫_ℝ)⁻¹ • T n-q0‖+‖w-w0‖ ≤ 112*eta := by
    change ‖(⟪n,T n⟫_ℝ)⁻¹ • T n-(‖n‖^2)⁻¹ • n‖+‖w-w0‖ ≤ 112*eta
    linarith
  have he := moving_sphere_leading_form_stability omega v b q0 w0
    ((⟪n,T n⟫_ℝ)⁻¹ • T n) w (112*eta) homega hv hov hb hn rfl ho
    (by rw [hw0,hq0norm]) hpair
  dsimp only
  convert he using 1 <;> (try dsimp only [n]) <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
