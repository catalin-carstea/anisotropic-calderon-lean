import Mathlib.Analysis.Normed.Module.Basic

/-! EXPANSION.json precedes the exact uniform-gain application and bound algebra. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem exists_uniform_bound_of_bounded_gain_pullback
    {V X Y U : Type*} [Norm V] [Norm X] [Norm Y] [Norm U]
    (P : X → Y → Prop) (R : U → Y → Prop)
    (hGain : ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : X) (y : Y), P x y →
      ∃ u : U, R u y ∧ ‖u‖ ≤ K * (‖y‖ + ‖x‖))
    (B : V → Y) (F : V → X)
    (hWeak : ∀ v : V, P (F v) (B v))
    (C : ℝ) (hC : 0 ≤ C)
    (hSum : ∀ v : V, ‖B v‖ + ‖F v‖ ≤ C * ‖v‖) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : V, ∃ u : U,
      R u (B v) ∧ ‖u‖ ≤ L * ‖v‖ := by
  obtain ⟨K,hK,hApply⟩ := hGain
  refine ⟨K*C,mul_nonneg hK hC,?_⟩
  intro v
  obtain ⟨u,hu,hNorm⟩ := hApply (F v) (B v) (hWeak v)
  refine ⟨u,hu,hNorm.trans ?_⟩
  calc
    K * (‖B v‖ + ‖F v‖) ≤ K * (C * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hSum v) hK
    _ = (K*C) * ‖v‖ := (mul_assoc _ _ _).symm

end OAI.AnisotropicCalderon.ExteriorSource
