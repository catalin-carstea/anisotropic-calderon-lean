import Calderon.ActualHarmonicLiftZeroDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual signed Banach-valued second Taylor remainder. This is calculus
in a fixed topology, not a sharp boundary trace or pseudodifferential claim. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def secondTaylorRemainder (F : ℝ → V) (r : ℝ) : V :=
  ∫ t : ℝ in (0 : ℝ)..1, (1-t) • deriv (deriv F) (t*r)

theorem signed_taylor_integral_remainder (F : ℝ → V) (r : ℝ)
    (hF : ∀ t ∈ uIcc (0 : ℝ) r, ContDiffAt ℝ ∞ F t) :
    F r = F 0 + r • deriv F 0 + r^2 • secondTaylorRemainder F r := by
  have hD (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) :
      ContDiffAt ℝ ∞ (deriv F) t := (hF t ht).derivWithin (by simp)
  have hDD (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) :
      ContDiffAt ℝ ∞ (deriv (deriv F)) t := (hD t ht).derivWithin (by simp)
  have hDc : ContinuousOn (deriv F) (uIcc (0 : ℝ) r) :=
    fun t ht => (hD t ht).continuousAt.continuousWithinAt
  have hDDc : ContinuousOn (deriv (deriv F)) (uIcc (0 : ℝ) r) :=
    fun t ht => (hDD t ht).continuousAt.continuousWithinAt
  have hFTC : (∫ t : ℝ in (0 : ℝ)..r, deriv F t) = F r - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => ((hF t ht).differentiableAt (by simp)).hasDerivAt)
      hDc.intervalIntegrable
  have hIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (a := (0 : ℝ)) (b := r) (u := fun t : ℝ => r-t)
    (u' := fun _ : ℝ => (-1 : ℝ)) (v := deriv F) (v' := deriv (deriv F))
    (by fun_prop) hDc
    (fun t ht => by
      convert (hasDerivAt_id t).const_sub r using 1 <;> simp)
    (fun t ht => ((hD t (mem_Icc_of_Ioo ht)).differentiableAt (by simp)).hasDerivAt)
    (intervalIntegrable_const) hDDc.intervalIntegrable
  simp only [sub_self, zero_smul, sub_zero, intervalIntegral.integral_smul,
    neg_one_smul, intervalIntegral.integral_neg, hFTC] at hIBP
  have hScale : (∫ t : ℝ in (0 : ℝ)..r, (r-t) • deriv (deriv F) t) =
      r^2 • secondTaylorRemainder F r := by
    have hChange := intervalIntegral.smul_integral_comp_mul_right
      (fun t : ℝ => (r-t) • deriv (deriv F) t) (a := (0 : ℝ)) (b := (1 : ℝ)) r
    simp only [zero_mul, one_mul] at hChange
    rw [← hChange]
    have hRewrite : (fun t : ℝ => (r-t*r) • deriv (deriv F) (t*r)) =
        fun t : ℝ => r • ((1-t) • deriv (deriv F) (t*r)) := by
      funext t
      rw [smul_smul]
      congr 1
      ring
    rw [hRewrite, intervalIntegral.integral_smul, smul_smul, ← pow_two]
    rfl
  rw [hScale] at hIBP
  rw [hIBP]
  abel

theorem norm_secondTaylorRemainder_le (F : ℝ → V) (r C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv F) (t*r)‖ ≤ C) :
    ‖secondTaylorRemainder F r‖ ≤ C/2 := by
  have hBound : ‖secondTaylorRemainder F r‖ ≤ ∫ t : ℝ in (0 : ℝ)..1, (1-t)*C := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards [] with t ht
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      exact mul_le_mul_of_nonneg_left (hb t ⟨ht.1.le,ht.2⟩) (sub_nonneg.mpr ht.2)
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hInt : (∫ t : ℝ in (0 : ℝ)..1, (1-t)*C) = C/2 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub
        (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
        (intervalIntegrable_const) (Continuous.intervalIntegrable continuous_id _ _), integral_one, integral_id]
    ring
  exact hBound.trans_eq hInt

theorem secondTaylorRemainder_zero (F : ℝ → V) :
    secondTaylorRemainder F 0 = (1/2 : ℝ) • deriv (deriv F) 0 := by
  simp only [secondTaylorRemainder, mul_zero]
  rw [intervalIntegral.integral_smul_const,
    intervalIntegral.integral_sub
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
      (intervalIntegrable_const) (Continuous.intervalIntegrable continuous_id _ _), integral_one, integral_id]
  norm_num

end OAI.AnisotropicCalderon.ConnectionError
