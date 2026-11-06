import Calderon.ActualAllAngularAtomNativeBudgets

/-! Scalar-only finite aggregation and common-cap enlargement. Native endpoint
norms and smoothness occur only in consumers of these complete order lemmas. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomScalarCaps

/-- Aggregate finitely many nonnegative caps for any increasing cap predicate. -/
theorem exists_finite_monotone_cap {ι : Type} [Fintype ι]
    (P : ι → ℝ → Prop)
    (hMono : ∀ i x y, x ≤ y → P i x → P i y)
    (hP : ∀ i, ∃ M : ℝ, 0 ≤ M ∧ P i M) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, P i M := by
  classical
  choose Mi hMi using hP
  let M : ℝ := ∑ i : ι, Mi i
  refine ⟨M, Finset.sum_nonneg (fun i _ => (hMi i).1), ?_⟩
  intro i
  have hOne : Mi i ≤ M := Finset.single_le_sum
    (fun j _ => (hMi j).1) (Finset.mem_univ i)
  exact hMono i (Mi i) M hOne (hMi i).2

/-- Five real caps admit a common enlargement at least one. No sign hypothesis
is needed, and the proof uses only the order laws for maximum. -/
theorem exists_five_real_upper_bounds (M1 M2 M3 M4 M5 : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ M1 ≤ M ∧ M2 ≤ M ∧ M3 ≤ M ∧ M4 ≤ M ∧ M5 ≤ M := by
  let M : ℝ := max 1 (max M1 (max M2 (max M3 (max M4 M5))))
  have hTail1 : max M1 (max M2 (max M3 (max M4 M5))) ≤ M :=
    le_max_right _ _
  have hTail2 : max M2 (max M3 (max M4 M5)) ≤ M :=
    (le_max_right _ _).trans hTail1
  have hTail3 : max M3 (max M4 M5) ≤ M :=
    (le_max_right _ _).trans hTail2
  have hTail4 : max M4 M5 ≤ M :=
    (le_max_right _ _).trans hTail3
  exact ⟨M, le_max_left _ _, (le_max_left _ _).trans hTail1,
    (le_max_left _ _).trans hTail2, (le_max_left _ _).trans hTail3,
    (le_max_left _ _).trans hTail4, (le_max_right _ _).trans hTail4⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAllAngularAtomScalarCaps
