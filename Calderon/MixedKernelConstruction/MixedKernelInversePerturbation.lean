import Calderon.MixedKernelConstruction.TaskInterface
import Calderon.MetricOperator
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff Topology

/-- The exact difference factorization for genuine right and left inverse operators. -/
theorem right_inverse_sub_left_inverse_factorization
    (P P0 M M0 : R3 →L[ℝ] R3)
    (hPM : ∀ U : R3, P (M U)=U) (hM0P0 : ∀ U : R3, M0 (P0 U)=U) :
    M-M0 = -(M0.comp (P-P0)).comp M := by
  apply ContinuousLinearMap.ext
  intro U
  change M U-M0 U = -(M0 ((P-P0) (M U)))
  simp only [ContinuousLinearMap.sub_apply,map_sub,hPM,hM0P0]
  abel

/-- The actual inverse and its difference have uniform quantitative bounds from the original perturbation. -/
theorem inverse_operator_perturbation_bounds
    (P P0 M M0 : R3 →L[ℝ] R3) (K delta : ℝ)
    (hPM : ∀ U : R3, P (M U)=U) (hM0P0 : ∀ U : R3, M0 (P0 U)=U)
    (hK : 0 ≤ K) (hM0 : ‖M0‖ ≤ K) (hDiff : ‖P-P0‖ ≤ delta) (hSmall : K*delta ≤ 1/2) :
    ‖M‖ ≤ 2*K ∧ ‖M-M0‖ ≤ 2*K^2*delta := by
  have hd : 0 ≤ delta := (norm_nonneg _).trans hDiff
  have hFactor := right_inverse_sub_left_inverse_factorization P P0 M M0 hPM hM0P0
  have hPoint (U : R3) : ‖M U-M0 U‖ ≤ (K*delta)*‖M U‖ := by
    have heq := congrArg (fun A : R3 →L[ℝ] R3 => A U) hFactor
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply] at heq
    rw [heq,norm_neg]
    calc
      ‖M0 ((P-P0) (M U))‖ ≤ ‖M0‖*‖(P-P0) (M U)‖ := M0.le_opNorm _
      _ ≤ ‖M0‖*(delta*‖M U‖) := mul_le_mul_of_nonneg_left
        (((P-P0).le_opNorm (M U)).trans (mul_le_mul_of_nonneg_right hDiff (norm_nonneg _))) (norm_nonneg _)
      _ ≤ K*(delta*‖M U‖) := mul_le_mul_of_nonneg_right hM0 (mul_nonneg hd (norm_nonneg _))
      _ = (K*delta)*‖M U‖ := by ring
  have hBound (U : R3) : ‖M U‖ ≤ (2*K)*‖U‖ := by
    have hM0U : ‖M0 U‖ ≤ K*‖U‖ := (M0.le_opNorm U).trans (mul_le_mul_of_nonneg_right hM0 (norm_nonneg U))
    have hTriangle : ‖M U‖ ≤ ‖M0 U‖+‖M U-M0 U‖ := by
      have hh := norm_add_le (M0 U) (M U-M0 U)
      have heq : M0 U+(M U-M0 U)=M U := by abel
      rw [heq] at hh
      exact hh
    have hHalf := mul_le_mul_of_nonneg_right hSmall (norm_nonneg (M U))
    linarith only [hM0U,hTriangle,hHalf,hPoint U]
  refine ⟨M.opNorm_le_bound (by positivity) hBound,?_⟩
  apply (M-M0).opNorm_le_bound (by positivity)
  intro U
  change ‖M U-M0 U‖ ≤ (2*K^2*delta)*‖U‖
  calc
    ‖M U-M0 U‖ ≤ (K*delta)*‖M U‖ := hPoint U
    _ ≤ (K*delta)*((2*K)*‖U‖) := mul_le_mul_of_nonneg_left (hBound U) (mul_nonneg hK hd)
    _ = (2*K^2*delta)*‖U‖ := by ring

/-- The perturbation bounds specialize to the GENUINE algebraic inverse at unit operators. -/
theorem ring_inverse_perturbation_bounds
    (P P0 : R3 →L[ℝ] R3) (hP : IsUnit P) (hP0 : IsUnit P0) (K delta : ℝ)
    (hK : 0 ≤ K) (hM0 : ‖Ring.inverse P0‖ ≤ K) (hDiff : ‖P-P0‖ ≤ delta)
    (hSmall : K*delta ≤ 1/2) :
    ‖Ring.inverse P‖ ≤ 2*K ∧ ‖Ring.inverse P-Ring.inverse P0‖ ≤ 2*K^2*delta := by
  apply inverse_operator_perturbation_bounds P P0 (Ring.inverse P) (Ring.inverse P0) K delta
    ?_ ?_ hK hM0 hDiff hSmall
  · intro U
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A U) (Ring.mul_inverse_cancel P hP)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh
  · intro U
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A U) (Ring.inverse_mul_cancel P0 hP0)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using hh

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
