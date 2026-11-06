import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualFirstAngularCoefficientCollection
lemma firstAngularCoefficient_collection {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r drift : ℝ) (q gamma eta : Fin 3 → Fin 3 → ℝ) (e m : Fin 3 → ℝ)
    (F N : M) (A R : Fin 3 → M) :
    r • ∑ a : Fin 3, ∑ b : Fin 3, q a b •
      ((-gamma a b) • F + e a • A b + e b • A a + eta a b • N) +
      (∑ a : Fin 3, m a • R a) + (r*drift) • F =
    (r*drift-r*∑ a : Fin 3, ∑ b : Fin 3, q a b*gamma a b) • F +
      (r*∑ a : Fin 3, ∑ b : Fin 3, q a b*eta a b) • N +
      (∑ c : Fin 3, (r*((∑ a : Fin 3, q a c*e a)+(∑ b : Fin 3, q c b*e b))) • A c) +
      ∑ a : Fin 3, m a • R a := by
  simp only [Fin.sum_univ_three,sub_smul,smul_add,smul_neg,add_smul,smul_smul,
    mul_add,add_mul,mul_sub,sub_mul,mul_neg,neg_mul,neg_smul,mul_assoc,mul_left_comm,mul_comm]
  abel


lemma defectFirstAngularCoefficient_collection {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r drift a1 : ℝ) (q gamma eta : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℝ)
    (F N : M) (D R : Fin 3 → M) :
    a1 • F - (2*r) • ∑ a : Fin 3, ∑ b : Fin 3, q a b • ((-gamma a b) • F + eta a b • N) -
      (∑ a : Fin 3, m a • (D a+R a)) - (2*r*drift) • F =
    (a1-2*(r*drift-r*∑ a : Fin 3, ∑ b : Fin 3, q a b*gamma a b)) • F -
      (2*(r*∑ a : Fin 3, ∑ b : Fin 3, q a b*eta a b)) • N -
      ∑ a : Fin 3, m a • (D a+R a) := by
  simp only [Fin.sum_univ_three,sub_smul,smul_add,smul_neg,add_smul,smul_smul,
    mul_add,add_mul,mul_sub,sub_mul,mul_neg,neg_mul,neg_smul,mul_assoc,mul_left_comm,mul_comm]
  abel

end OAI.AnisotropicCalderon.ActualFirstAngularCoefficientCollection
