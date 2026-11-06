import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem eq_of_coercive_apply_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) (u v : E)
    (h : ∀ w : E, B u w = B v w) : u = v := by
  by_contra huv
  obtain ⟨c, hc, hcoercive⟩ := hB
  have hZero : B (u - v) (u - v) = 0 := by
    rw [show B (u - v) = B u - B v from map_sub B u v,
      ContinuousLinearMap.sub_apply, h (u - v), sub_self]
  have hp : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  have hle : c * ‖u - v‖ * ‖u - v‖ ≤ 0 :=
    (hcoercive (u - v)).trans_eq hZero
  exact (not_lt_of_ge hle) (mul_pos (mul_pos hc hp) hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
