import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OAI.AnisotropicCalderon

theorem summable_rpow_of_polynomial_bound {μ : ℕ → ℝ} {a C : ℝ} {N : ℕ}
    (hμ : ∀ j, 0 ≤ μ j) (ha : 0 < a) (hC : 0 ≤ C)
    (hNa : 1 < (N : ℝ) * a)
    (hbound : ∀ j, μ j ≤ C * (j + 1 : ℝ) ^ (-(N : ℝ))) :
    Summable (fun j => μ j ^ a) := by
  have hs : Summable (fun j : ℕ => (j + 1 : ℝ) ^ (-(N : ℝ) * a)) := by
    have h := (Real.summable_nat_rpow.mpr (show -(N : ℝ) * a < -1 by linarith))
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr h
  apply Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (hμ j) a)
    (fun j => ?_) (hs.mul_left (C ^ a))
  calc
    μ j ^ a ≤ (C * (j + 1 : ℝ) ^ (-(N : ℝ))) ^ a :=
      Real.rpow_le_rpow (hμ j) (hbound j) ha.le
    _ = C ^ a * (j + 1 : ℝ) ^ (-(N : ℝ) * a) := by
      rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul (by positivity)]

theorem summable_rpow_of_forall_polynomial_bound {μ : ℕ → ℝ} {a : ℝ}
    (hμ : ∀ j, 0 ≤ μ j) (ha : 0 < a)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, μ j ≤ C * (j + 1 : ℝ) ^ (-(N : ℝ))) :
    Summable (fun j => μ j ^ a) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / a)
  obtain ⟨C, hC, hbound⟩ := hdecay N
  apply summable_rpow_of_polynomial_bound hμ ha hC ?_ hbound
  exact (div_lt_iff₀ ha).mp hN

theorem summable_of_norm_le_rpow_of_forall_polynomial_bound
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℕ → E} {μ : ℕ → ℝ} {a M : ℝ}
    (hμ : ∀ j, 0 ≤ μ j) (ha : 0 < a)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, μ j ≤ C * (j + 1 : ℝ) ^ (-(N : ℝ)))
    (hbound : ∀ j, ‖v j‖ ≤ M * μ j ^ a) : Summable v := by
  exact ((summable_rpow_of_forall_polynomial_bound hμ ha hdecay).mul_left M).of_norm_bounded hbound

theorem tsum_rpow_le_of_exponent_ge_of_forall_polynomial_bound
    {μ : ℕ → ℝ} {p a : ℝ}
    (hμ : ∀ j, 0 ≤ μ j) (hμone : ∀ j, μ j ≤ 1)
    (hp : 0 < p) (hpa : p ≤ a)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ j, μ j ≤ C * (j + 1 : ℝ) ^ (-(N : ℝ))) :
    ∑' j, μ j ^ a ≤ ∑' j, μ j ^ p := by
  apply Summable.tsum_le_tsum
    (fun j => Real.rpow_le_rpow_of_exponent_ge' (hμ j) (hμone j) hp.le hpa)
    (summable_rpow_of_forall_polynomial_bound hμ (hp.trans_le hpa) hdecay)
    (summable_rpow_of_forall_polynomial_bound hμ hp hdecay)

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.summable_rpow_of_polynomial_bound
#print axioms OAI.AnisotropicCalderon.summable_rpow_of_forall_polynomial_bound
#print axioms OAI.AnisotropicCalderon.summable_of_norm_le_rpow_of_forall_polynomial_bound
#print axioms OAI.AnisotropicCalderon.tsum_rpow_le_of_exponent_ge_of_forall_polynomial_bound
