import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon

lemma integral_mul_eq_of_forall_eq
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w f g : X → ℝ)
    (h : ∀ x : X, f x = g x) :
    (∫ x : X, w x * f x ∂μ) = ∫ x : X, w x * g x ∂μ := by
  have hfg : f = g := funext h
  cases hfg
  rfl

end OAI.AnisotropicCalderon
