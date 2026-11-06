import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualFirstAngularCoefficientAlgebra

lemma firstAngularCoefficient_collection {M : Type*} [AddCommGroup M] [Module ℝ M]
    (e m : Fin 3 → ℝ) (D R : Fin 3 → M) (Z F : M) (a b : ℝ) :
    ((-(∑ i : Fin 3, e i • D i) - (∑ i : Fin 3, e i • R i)) +
      (-(∑ i : Fin 3, e i • D i) - (∑ i : Fin 3, e i • R i))) +
    (a • F - Z - (∑ i : Fin 3, m i • (D i+R i)) - (2*b) • F) =
      (∑ i : Fin 3, (-2*e i-m i) • (D i+R i)) - Z + (a-2*b) • F := by
  simp only [Fin.sum_univ_three, sub_smul, smul_add, neg_mul, neg_smul, mul_smul, two_smul]
  abel

end OAI.AnisotropicCalderon.ActualFirstAngularCoefficientAlgebra
