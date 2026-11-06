import Calderon.StrongSolutionLift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open ContinuousLinearMap
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X H V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem isInvertible_of_strongLift (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (hS : Function.Injective S) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖)
    (L : X →L[ℝ] H) (hL : ∀ x, S (L x) = i x) : L.IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (operator_comp_strongLift i S hi hS C h L hL)
    (strongLift_comp_operator i S hi C h L hL)

theorem inverse_eq_strongLift (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (hS : Function.Injective S) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖)
    (L : X →L[ℝ] H) (hL : ∀ x, S (L x) = i x) :
    L.inverse = strongLift i S hi C h :=
  ContinuousLinearMap.inverse_eq
    (operator_comp_strongLift i S hi hS C h L hL)
    (strongLift_comp_operator i S hi C h L hL)

variable [CompleteSpace X]

theorem contDiffOn_banachInverseFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
    (A : E → X →L[ℝ] H) (s : Set E)
    (hA : ContDiffOn ℝ n A s) (hi : ∀ x ∈ s, (A x).IsInvertible) :
    ContDiffOn ℝ n (fun x => (A x).inverse) s := by
  intro x hx
  exact (hi x hx).contDiffAt_map_inverse.comp_contDiffWithinAt x (hA x hx)

theorem contDiffOn_banachWeightedInverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    (A : E → X →L[ℝ] H) (M : E → F →L[ℝ] H) (s : Set E)
    (hA : ContDiffOn ℝ n A s) (hi : ∀ x ∈ s, (A x).IsInvertible)
    (hM : ContDiffOn ℝ n M s) :
    ContDiffOn ℝ n (fun x => (A x).inverse.comp (M x)) s :=
  (contDiffOn_banachInverseFamily A s hA hi).clm_comp hM

theorem continuousOn_banachInverseFamily {Z : Type*} [TopologicalSpace Z]
    (A : Z → X →L[ℝ] H) (s : Set Z)
    (hA : ContinuousOn A s) (hi : ∀ x ∈ s, (A x).IsInvertible) :
    ContinuousOn (fun x => (A x).inverse) s := by
  intro x hx
  exact ((hi x hx).contDiffAt_map_inverse (n := 0)).continuousAt.comp_continuousWithinAt
    (hA x hx)

theorem uniform_norm_banachInverseFamily {Z : Type*} [TopologicalSpace Z]
    (A : Z → X →L[ℝ] H) (s : Set Z) (hs : IsCompact s)
    (hA : ContinuousOn A s) (hi : ∀ x ∈ s, (A x).IsInvertible) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ s, ‖(A x).inverse‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn
    (continuousOn_banachInverseFamily A s hA hi)
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

end OAI.AnisotropicCalderon.DirichletFamily
