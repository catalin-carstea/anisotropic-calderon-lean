import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
open ContinuousLinearMap
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X H V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The unique strong lift of an actual bounded weak solution map. -/
def strongLiftLinearMap (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) : H →ₗ[ℝ] X where
  toFun f := Classical.choose (h f)
  map_add' f g := hi (by
    rw [(Classical.choose_spec (h (f + g))).1, map_add, map_add,
      (Classical.choose_spec (h f)).1, (Classical.choose_spec (h g)).1])
  map_smul' c f := hi (by
    rw [(Classical.choose_spec (h (c • f))).1, map_smul, map_smul,
      (Classical.choose_spec (h f)).1]
    rfl)

theorem strongLiftLinearMap_projection (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) (f : H) :
    i (strongLiftLinearMap i S hi C h f) = S f :=
  (Classical.choose_spec (h f)).1

theorem norm_strongLiftLinearMap_apply_le (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) (f : H) :
    ‖strongLiftLinearMap i S hi C h f‖ ≤ C * ‖f‖ :=
  (Classical.choose_spec (h f)).2

/-- Continuity follows from the same fixed regularity bound. -/
def strongLift (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) : H →L[ℝ] X :=
  (strongLiftLinearMap i S hi C h).mkContinuous C
    (norm_strongLiftLinearMap_apply_le i S hi C h)

theorem strongLift_projection (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) (f : H) :
    i (strongLift i S hi C h f) = S f :=
  strongLiftLinearMap_projection i S hi C h f

theorem norm_strongLift_le (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖) :
    ‖strongLift i S hi C h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (norm_strongLiftLinearMap_apply_le i S hi C h)

theorem strongLift_unique (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖)
    (f : H) (x : X) (hx : i x = S f) : strongLift i S hi C h f = x :=
  hi ((strongLift_projection i S hi C h f).trans hx.symm)

theorem strongLift_comp_operator (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖)
    (L : X →L[ℝ] H) (hL : ∀ x, S (L x) = i x) :
    (strongLift i S hi C h).comp L = ContinuousLinearMap.id ℝ X := by
  ext x
  exact strongLift_unique i S hi C h (L x) x (hL x).symm

theorem operator_comp_strongLift (i : X →L[ℝ] V) (S : H →L[ℝ] V)
    (hi : Function.Injective i) (hS : Function.Injective S) (C : ℝ)
    (h : ∀ f, ∃ x, i x = S f ∧ ‖x‖ ≤ C * ‖f‖)
    (L : X →L[ℝ] H) (hL : ∀ x, S (L x) = i x) :
    L.comp (strongLift i S hi C h) = ContinuousLinearMap.id ℝ H := by
  ext f
  apply hS
  exact (hL _).trans (strongLift_projection i S hi C h f)

end OAI.AnisotropicCalderon.DirichletFamily
