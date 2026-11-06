import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators
namespace OAI.AnisotropicCalderon.FiniteLinearCombinationGraph

/-- Exact finite linear graph transport, including arbitrary signed real coefficients. -/
theorem eq_linearMap_apply_of_weighted_sums
    {R E F ι : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F]
    (T : E →ₗ[R] F) (s : Finset ι) (a : ι → R) (u : ι → E) (v : ι → F)
    (x : E) (y : F)
    (hx : x = ∑ i ∈ s, a i • u i) (hy : y = ∑ i ∈ s, a i • v i)
    (hTerm : ∀ i ∈ s, v i = T (u i)) : y = T x := by
  have hTerms : (∑ i ∈ s, a i • v i) = ∑ i ∈ s, T (a i • u i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (congrArg (fun z : F => a i • z) (hTerm i hi)).trans
      (T.map_smul (a i) (u i)).symm
  have hMap : T (∑ i ∈ s, a i • u i) = ∑ i ∈ s, T (a i • u i) :=
    map_sum T (fun i => a i • u i) s
  exact hy.trans (hTerms.trans (hMap.symm.trans (congrArg T hx.symm)))

end OAI.AnisotropicCalderon.FiniteLinearCombinationGraph

#print axioms OAI.AnisotropicCalderon.FiniteLinearCombinationGraph.eq_linearMap_apply_of_weighted_sums
