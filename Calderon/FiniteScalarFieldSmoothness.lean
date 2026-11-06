import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff
namespace OAI.AnisotropicCalderon.FiniteScalarFieldSmoothness

theorem contDiff_neg_triple_sum_smul
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : Fin 3 → Fin 3 → Fin 3 → X → ℝ) (v : Fin 3 → X → E)
    (hc : ∀ i j a : Fin 3, ContDiff ℝ ∞ (c i j a))
    (hv : ∀ a : Fin 3, ContDiff ℝ ∞ (v a)) :
    ContDiff ℝ ∞ (fun x : X => -(∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, (c i j a x) • v a x)) := by
  exact (ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => ContDiff.sum
    (fun a _ => (hc i j a).smul (hv a))))).neg

end OAI.AnisotropicCalderon.FiniteScalarFieldSmoothness
