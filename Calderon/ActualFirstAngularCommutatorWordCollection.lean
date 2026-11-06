import Calderon.ActualFiniteHarmonicCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ActualFirstAngularCommutatorWordCollection
open SphereHarmonic ActualFiniteHarmonicCore

lemma firstAngular_commutator_four_block_collection {A : Type*} [Ring A]
    (d d2 : A) (m n k P Q R : Fin 3 → A)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → A) (E : Fin 3 → Fin 3 → A) :
    d * -(∑ a : Fin 3, m a * P a) +
      (∑ c : Fin 3, k c * ∑ a : Fin 3, ∑ b : Fin 3, m a * Gamma c b a * Q b) +
      (∑ b : Fin 3, n b * (-d2 * R b - ∑ a : Fin 3, m a * E a b)) =
    -(∑ a : Fin 3, d * m a * P a) +
      (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, k c * m a * Gamma c b a * Q b) -
      (∑ b : Fin 3, n b * d2 * R b) -
      ∑ b : Fin 3, ∑ a : Fin 3, n b * m a * E a b := by
  simp only [Finset.mul_sum,mul_neg,neg_mul,mul_sub,Finset.sum_neg_distrib,
    Finset.sum_sub_distrib,mul_assoc]
  abel

lemma core_firstAngular_commutator_four_block_collection
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d d2 : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (m n k P Q R : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (Gamma : Fin 3 → Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (E : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
    d * -(∑ a : Fin 3, m a * P a) +
      (∑ c : Fin 3, k c * ∑ a : Fin 3, ∑ b : Fin 3, m a * Gamma c b a * Q b) +
      (∑ b : Fin 3, n b * (-d2 * R b - ∑ a : Fin 3, m a * E a b)) =
    -(∑ a : Fin 3, d * m a * P a) +
      (∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, k c * m a * Gamma c b a * Q b) -
      (∑ b : Fin 3, n b * d2 * R b) -
      ∑ b : Fin 3, ∑ a : Fin 3, n b * m a * E a b := by
  exact firstAngular_commutator_four_block_collection d d2 m n k P Q R Gamma E

end OAI.AnisotropicCalderon.ActualFirstAngularCommutatorWordCollection
