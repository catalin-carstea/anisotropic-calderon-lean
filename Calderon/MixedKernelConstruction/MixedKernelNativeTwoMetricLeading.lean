import Calderon.MixedKernelConstruction.TaskInterface
import Calderon.MixedKernelConstruction.MixedKernelMetricImaginaryNormalization
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError
open scoped InnerProductSpace

/-- Normalize BOTH actual metric characteristic pairs, retaining the original profile vector and its true Jacobi error. -/
theorem native_two_metric_leading_lower_bound
    (T1 R1 T2 R2 : R3 →L[ℝ] R3) (z b e u w : R3) (eta1 eta2 : ℝ)
    (hz : ‖z‖=1) (hb : ‖b‖ ≤ 1/8) (he : ‖e‖ ≤ 1/8)
    (heta1 : eta1 ≤ 1/320) (heta2 : eta2 ≤ 1/320)
    (hT1 : ‖T1-ContinuousLinearMap.id ℝ R3‖ ≤ eta1)
    (hT2 : ‖T2-ContinuousLinearMap.id ℝ R3‖ ≤ eta2)
    (hInv1 : ∀ X : R3, T1 (R1 X)=X) (hInv2 : ∀ X : R3, T2 (R2 X)=X)
    (huOrth : ⟪z,u⟫_ℝ=0) (huLength : ⟪u,R1 u⟫_ℝ=(⟪z,T1 z⟫_ℝ)⁻¹)
    (hwOrth : ⟪z+(b+e),w⟫_ℝ=0)
    (hwLength : ⟪w,R2 w⟫_ℝ=(⟪z+(b+e),T2 (z+(b+e))⟫_ℝ)⁻¹) :
    let n := z+(b+e)
    let q1 := (⟪z,T1 z⟫_ℝ)⁻¹ • T1 z
    let q2 := (⟪n,T2 n⟫_ℝ)⁻¹ • T2 n
    ‖q1‖ ≤ 2 ∧ ‖q2‖ ≤ 4 ∧ ‖u‖ ≤ 4 ∧ ‖w‖ ≤ 4 ∧ (1/2 : ℝ) ≤ ‖q2‖ ∧
      -1120*eta1-1792*‖b+e‖*eta2-200704*eta2^2-264*‖e‖ ≤ 
        ‖q1-q2‖^2+‖u-w‖^2-2*(⟪b,q2⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
  intro n q1 q2
  have heta10 : 0 ≤ eta1 := (norm_nonneg _).trans hT1
  have heta20 : 0 ≤ eta2 := (norm_nonneg _).trans hT2
  have hbE : ‖b+e‖ ≤ 1/4 := (norm_add_le b e).trans (by linarith)
  have hn0 : (1/2 : ℝ) ≤ ‖n‖ := by
    have hh := norm_sub_norm_le z (-(b+e))
    simp only [hz,norm_neg,sub_neg_eq_add] at hh
    change (1/2 : ℝ) ≤ ‖z+(b+e)‖
    linarith
  have hn1 : ‖n‖ ≤ 2 := by
    have hh := norm_add_le z (b+e)
    rw [hz] at hh
    change ‖z+(b+e)‖ ≤ 2
    linarith
  have hnPos : 0<‖n‖ := by linarith
  have hnNe : n≠0 := norm_pos_iff.mp hnPos
  have hz0 : (1/2 : ℝ) ≤ ‖z‖ := by rw [hz];norm_num
  have hz1 : ‖z‖ ≤ 2 := by rw [hz];norm_num
  obtain ⟨u0,hu0Orth,hu0Len,hu0Near⟩ := exists_metric_characteristic_comparison T1 R1 z u eta1 heta1 hT1 hInv1 hz0 hz1 huOrth huLength
  have hu0Norm : ‖u0‖=1 := by simpa only [hz,inv_one] using hu0Len
  have hq1Near : ‖q1-z‖ ≤ 32*eta1 := by
    simpa only [hz,one_pow,inv_one,one_smul] using
      (normalized_operator_vector_near_identity T1 z eta1 (by linarith) hT1 hz0 hz1).2
  have hq1Bound : ‖q1‖ ≤ 2 := by
    have hh : ‖q1‖ ≤ ‖z‖+‖q1-z‖ := by
      have h := norm_add_le z (q1-z)
      have hEq : z+(q1-z)=q1 := by abel
      rw [hEq] at h
      exact h
    rw [hz] at hh
    linarith
  let q20 := (‖n‖^2)⁻¹ • n
  have hq20Bound : ‖q20‖ ≤ 2 :=
    (normalized_sum_reference_bounds z (b+e) q20 hz hbE hnNe rfl).1
  obtain ⟨hDen,hq2Near⟩ := normalized_operator_vector_near_identity T2 n eta2 (by linarith) hT2 hn0 hn1
  have hq2Bound : ‖q2‖ ≤ 4 := by
    have hh : ‖q2‖ ≤ ‖q20‖+‖q2-q20‖ := by
      have h := norm_add_le q20 (q2-q20)
      have hEq : q20+(q2-q20)=q2 := by abel
      rw [hEq] at h
      exact h
    change ‖q2-q20‖ ≤ 32*eta2 at hq2Near
    linarith
  have hInner : ⟪n,q2⟫_ℝ=1 := by
    have hDenNe : ⟪n,T2 n⟫_ℝ≠0 := ne_of_gt (by linarith)
    change ⟪n,(⟪n,T2 n⟫_ℝ)⁻¹ • T2 n⟫_ℝ=1
    rw [real_inner_smul_right,inv_mul_cancel₀ hDenNe]
  have hq2Lower : (1/2 : ℝ) ≤ ‖q2‖ := by
    have hh := real_inner_le_norm n q2
    rw [hInner] at hh
    have hm := mul_le_mul_of_nonneg_right hn1 (norm_nonneg q2)
    linarith
  have huBound : ‖u‖ ≤ 4 := by
    have hh := (metric_characteristic_length_error T1 R1 z u eta1 (by linarith) hT1 hInv1 hz0 hz1 huLength).1
    nlinarith only [hh,norm_nonneg u]
  have hwBound : ‖w‖ ≤ 4 := by
    have hh := (metric_characteristic_length_error T2 R2 n w eta2 (by linarith) hT2 hInv2 hn0 hn1 hwLength).1
    nlinarith only [hh,norm_nonneg w]
  have hSecond := moving_sphere_metric_normalization_stability T2 R2 z u0 (b+e) w eta2
    hz hu0Norm hu0Orth hbE heta2 hT2 hInv2 hwOrth hwLength
  change -16*(112*‖b+e‖*eta2+(112*eta2)^2) ≤ 
    ‖z-q2‖^2+‖u0-w‖^2-2*(⟪b+e,q2⟫_ℝ^2+⟪b+e,w⟫_ℝ^2) at hSecond
  have hRefQ : ‖z-q2‖ ≤ 5 := (norm_sub_le z q2).trans (by rw [hz];linarith)
  have hRefU : ‖u0-w‖ ≤ 5 := (norm_sub_le u0 w).trans (by rw [hu0Norm];linarith)
  have hErrQ : ‖z-q1‖ ≤ 32*eta1 := by rw [norm_sub_rev];exact hq1Near
  have hErrU : ‖u0-u‖ ≤ 80*eta1 := by rw [norm_sub_rev];exact hu0Near
  have hLossQ : ‖z-q2‖^2-320*eta1 ≤ ‖q1-q2‖^2 := by
    have hh := norm_sub_square_lower (z-q2) (z-q1)
    rw [show z-q2-(z-q1)=q1-q2 by abel] at hh
    have hm : 2*‖z-q2‖*‖z-q1‖ ≤ 320*eta1 := by
      calc _  ≤  2*5*(32*eta1) := by gcongr
           _ = _ := by ring
    linarith
  have hLossU : ‖u0-w‖^2-800*eta1 ≤ ‖u-w‖^2 := by
    have hh := norm_sub_square_lower (u0-w) (u0-u)
    rw [show u0-w-(u0-u)=u-w by abel] at hh
    have hm : 2*‖u0-w‖*‖u0-u‖ ≤ 800*eta1 := by
      calc _  ≤  2*5*(80*eta1) := by gcongr
           _ = _ := by ring
    linarith
  have hProfile (Q : R3) (hQ : ‖Q‖ ≤ 4) : ⟪b,Q⟫_ℝ^2 ≤ ⟪b+e,Q⟫_ℝ^2+66*‖e‖ := by
    have hh := inner_square_perturbation_bound Q (b+e) b (by linarith)
    have hInner1 : ⟪Q,b⟫_ℝ=⟪b,Q⟫_ℝ := real_inner_comm _ _
    have hInner2 : ⟪Q,b+e⟫_ℝ=⟪b+e,Q⟫_ℝ := real_inner_comm _ _
    rw [hInner1,hInner2,show b-(b+e)=-e by abel,norm_neg] at hh
    have hQSq : ‖Q‖^2 ≤ 16 := by nlinarith only [hQ,norm_nonneg Q]
    have hm1 := mul_le_mul_of_nonneg_right hQSq (norm_nonneg e)
    have hm2 := mul_le_mul_of_nonneg_right hQSq (sq_nonneg ‖e‖)
    have heSq : ‖e‖^2 ≤ ‖e‖/8 := by
      have h := mul_le_mul_of_nonneg_right he (norm_nonneg e)
      nlinarith only [h]
    nlinarith only [hh,hm1,hm2,heSq]
  refine ⟨hq1Bound,hq2Bound,huBound,hwBound,hq2Lower,?_⟩
  have hPq := hProfile q2 hq2Bound
  have hPw := hProfile w hwBound
  nlinarith only [hSecond,hLossQ,hLossU,hPq,hPw]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
