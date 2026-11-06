import Calderon.ActualModelCommutatorWords
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Defs

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualModelCommutatorWords
variable {A : Type*} [Ring A]

lemma modelFirstOrder_referenceAdjoint_decomposition [Module ℝ A]
    (d D : Fin 3 → A) (W1 W2 : A) (E : Fin 3 → Fin 3 → A) (K P : Fin 3 → A) :
    (∑ a : Fin 3, D a * ((-1 : ℝ) •
      (W1 * ((∑ j : Fin 3, E a j * d j) + K a)) + P a * W2)) =
    modelFirstOrder d (fun j => ∑ a : Fin 3, ((-1 : ℝ) • (D a * W1)) * E a j)
      (∑ a : Fin 3, D a * ((-1 : ℝ) • (W1 * K a) + P a * W2)) := by
  simp only [modelFirstOrder, neg_one_smul, Fin.sum_univ_three]
  noncomm_ring

lemma modelFirstOrder_firstDefect (d H K V : Fin 3 → A) (H0 K0 W : A) :
    2 * (modelFirstOrder d K K0 - modelFirstOrder d H H0) + modelFirstOrder d V W =
      modelFirstOrder d (fun j => 2 * (K j-H j)+V j) (2 * (K0-H0)+W) := by
  simp only [modelFirstOrder, Fin.sum_univ_three]
  noncomm_ring

end OAI.AnisotropicCalderon.ActualModelCommutatorWords
