import Calderon.JacobiIndex
import Mathlib.Tactic

open Set
namespace OAI.AnisotropicCalderon.JacobiIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem abs_indexIntegral_operator_sub_norm_sq_le (j j' : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (r K : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (-(r^2) • R s (j s)) s)
    (hf : ContinuousOn (fun s => -(r^2) • R s (j s)) (Icc 0 1))
    (hK : 0 ≤ K) (hsmall : K*r^2 ≤ 1)
    (hR : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K) :
    |indexIntegral j j' (fun s => -(r^2) • R s (j s))-‖j 1-j 0‖^2| ≤
      2*K*r^2*(endpointSize j)^2 := by
  have hforce : ∀ s ∈ Icc 0 1, ‖-(r^2) • R s (j s)‖ ≤ (K*r^2)*‖j s‖ := by
    intro s hs
    calc
      ‖-(r^2) • R s (j s)‖ = r^2*‖R s (j s)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg r)]
      _ ≤ r^2*(K*‖j s‖) := mul_le_mul_of_nonneg_left
        (((R s).le_opNorm (j s)).trans (mul_le_mul_of_nonneg_right (hR s hs) (norm_nonneg _)))
        (sq_nonneg r)
      _ = (K*r^2)*‖j s‖ := by ring
  simpa only [mul_assoc] using
    abs_indexIntegral_sub_norm_sq_le j j' (fun s => -(r^2) • R s (j s))
      (K*r^2) hj hj' hf (mul_nonneg hK (sq_nonneg r)) hsmall hforce

theorem abs_indexIntegral_continuous_operator_sub_norm_sq_le (j j' : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (r K : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (-(r^2) • R s (j s)) s)
    (hRC : ContinuousOn R (Icc 0 1))
    (hK : 0 ≤ K) (hsmall : K*r^2 ≤ 1)
    (hR : ∀ s ∈ Icc 0 1, ‖R s‖ ≤ K) :
    |indexIntegral j j' (fun s => -(r^2) • R s (j s))-‖j 1-j 0‖^2| ≤
      2*K*r^2*(endpointSize j)^2 := by
  have hc : ContinuousOn j (Icc 0 1) :=
    fun s hs => (hj s hs).continuousAt.continuousWithinAt
  have hf : ContinuousOn (fun s => -(r^2) • R s (j s)) (Icc 0 1) :=
    continuous_const.continuousOn.smul (hRC.clm_apply hc)
  exact abs_indexIntegral_operator_sub_norm_sq_le j j' R r K hj hj' hf hK hsmall hR

#print axioms abs_indexIntegral_continuous_operator_sub_norm_sq_le

#print axioms abs_indexIntegral_operator_sub_norm_sq_le
end OAI.AnisotropicCalderon.JacobiIntegral
