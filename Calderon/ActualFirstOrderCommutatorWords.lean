import Calderon.ActualModelCommutatorWords

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualModelCommutatorWords
variable {A : Type*} [Ring A]

def firstFirstSecondBaseWords (d H B : Fin 3 → A) : A :=
  ∑ i : Fin 3, ∑ j : Fin 3, commutator (H i) (B j) * d i * d j

def firstFirstFirstBaseWords (d H B : Fin 3 → A) (H0 B0 : A) : A :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    (H i * coefficientDerivative (d i) (B j) * d j -
      B j * coefficientDerivative (d j) (H i) * d i)) +
  (∑ i : Fin 3, commutator (H i) B0 * d i) +
  (∑ j : Fin 3, commutator H0 (B j) * d j)

def firstFirstZeroBaseWords (d H B : Fin 3 → A) (H0 B0 : A) : A :=
  (∑ i : Fin 3, H i * coefficientDerivative (d i) B0) -
  (∑ j : Fin 3, B j * coefficientDerivative (d j) H0) + commutator H0 B0

theorem first_first_order_commutator_words (d H B : Fin 3 → A) (H0 B0 : A)
    (hd : ∀ i j, Commute (d i) (d j)) :
    commutator (modelFirstOrder d H H0) (modelFirstOrder d B B0) =
      firstFirstSecondBaseWords d H B + firstFirstFirstBaseWords d H B H0 B0 +
        firstFirstZeroBaseWords d H B H0 B0 := by
  have hff (i j : Fin 3) := commutator_first_first (d i) (d j) (H i) (B j) (hd i j)
  simp only [modelFirstOrder, commutator_add_left, commutator_add_right,
    commutator_sum_left, commutator_sum_right]
  simp_rw [hff, commutator_first_zero, commutator_zero_first]
  simp only [firstFirstSecondBaseWords, firstFirstFirstBaseWords, firstFirstZeroBaseWords,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Fin.sum_univ_three]
  abel

end OAI.AnisotropicCalderon.ActualModelCommutatorWords
