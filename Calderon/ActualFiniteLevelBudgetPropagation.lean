import Calderon.MixedKernelConstruction.MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_finite_level_budget_propagation
    {X:Type} (K Seed:Set X) (level:X→ℝ) (lo hi delta A:ℝ)
    (hdelta:0 < delta) (hA:1 ≤ A) (hLevel:∀ x∈K,lo ≤ level x ∧ level x ≤ hi) :
    ∃ N:ℕ,∀ M:ℝ,0 ≤ M → ∀ u:X→ℝ,(∀ x∈Seed,u x ≤ M) →
      (∀ x∈K,x∉Seed → ∃ J:Set X,
        (∀ y∈J,y∈Seed ∨ (y∈K ∧ level x+delta ≤ level y)) ∧
        ∀ T:ℝ,0 ≤ T → (∀ y∈J,u y ≤ T) → u x ≤ A*T) →
      ∀ x∈K,u x ≤ A^N*M := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((hi+delta-lo)/delta)
  have hNlevel:hi+delta-(N:ℝ)*delta ≤ lo := by
    rw [div_lt_iff₀ hdelta] at hN
    linarith
  refine ⟨N,?_⟩
  intro M hM u hSeed hStep
  have hPow:∀ n:ℕ,M ≤ A^n*M := fun n =>
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hA) hM)
  have hLayers:∀ n:ℕ,∀ x∈K,hi+delta-(n:ℝ)*delta ≤ level x → u x ≤ A^n*M := by
    intro n
    induction n with
    | zero =>
      intro x hx hxl
      have hxhi:level x ≤ hi := (hLevel x hx).2
      norm_num only [Nat.cast_zero,zero_mul,sub_zero] at hxl
      linarith only [hxl,hxhi,hdelta]
    | succ n ih =>
      intro x hx hxl
      by_cases hxSeed:x∈Seed
      · exact (hSeed x hxSeed).trans (hPow (n+1))
      · obtain ⟨J,hJ,hEstimate⟩ := hStep x hx hxSeed
        have hT:0 ≤ A^n*M := mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) hM
        have hBudget:∀ y∈J,u y ≤ A^n*M := by
          intro y hy
          rcases hJ y hy with hySeed | ⟨hyK,hGain⟩
          · exact (hSeed y hySeed).trans (hPow n)
          · apply ih y hyK
            have hcast:((n+1:ℕ):ℝ)=(n:ℝ)+1 := by push_cast;ring
            rw [hcast] at hxl
            linarith only [hxl,hGain]
        have h:=hEstimate (A^n*M) hT hBudget
        exact h.trans_eq (by rw [pow_succ];ring)
  intro x hx
  exact hLayers N x hx (hNlevel.trans (hLevel x hx).1)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
