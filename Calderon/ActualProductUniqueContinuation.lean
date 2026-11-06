import Calderon.CollaboratorUniqueContinuationProofOct17

/-! Actual separated-operator uniqueness on a product box, for Main M1 mixed-germ gluing.
No R6 unique-continuation premise. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon

theorem eq_zero_on_product_of_separately_divCoeffGrad_eq_zero
    (U V : Set R3) (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V)
    (A B : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContDiffOn ℝ ∞ A U) (hAp : ∀ x ∈ U, (A x).PosDef)
    (hB : ContDiffOn ℝ ∞ B V) (hBp : ∀ y ∈ V, (B y).PosDef)
    (F : R3 → R3 → ℝ)
    (hFx : ∀ y ∈ V, ContDiffOn ℝ ∞ (fun x => F x y) U)
    (hLx : ∀ y ∈ V, ∀ x ∈ U, divCoeffGrad A (fun z => F z y) x = 0)
    (hFy : ∀ x ∈ U, ContDiffOn ℝ ∞ (F x) V)
    (hLy : ∀ x ∈ U, ∀ y ∈ V, divCoeffGrad B (F x) y = 0)
    (U0 V0 : Set R3) (hU0 : IsOpen U0) (hU0n : U0.Nonempty) (hU0U : U0 ⊆ U)
    (hV0 : IsOpen V0) (hV0n : V0.Nonempty) (hV0V : V0 ⊆ V)
    (hZero : ∀ x ∈ U0, ∀ y ∈ V0, F x y = 0) :
    ∀ x ∈ U, ∀ y ∈ V, F x y = 0 := by
  have hFirst : ∀ y ∈ V0, ∀ x ∈ U, F x y = 0 := by
    intro y hy
    exact uniqueContinuation U hU hUc A hA hAp (fun x => F x y)
      (hFx y (hV0V hy)) (hLx y (hV0V hy)) U0 hU0 hU0n hU0U
      (fun x hx => hZero x hx y hy)
  intro x hx
  exact uniqueContinuation V hV hVc B hB hBp (F x) (hFy x hx) (hLy x hx)
    V0 hV0 hV0n hV0V (fun y hy => hFirst y hy x hx)

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.eq_zero_on_product_of_separately_divCoeffGrad_eq_zero
