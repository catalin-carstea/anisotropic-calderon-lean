import Calderon.ActualFiniteHarmonicCore
import Calderon.ActualModelCommutatorWords
import Mathlib.Algebra.Module.LinearMap.End

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma core_first_second_order_commutator_words
    (d H : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (H0 : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (a : Fin 3 → Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (B : Fin 3 → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (C : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hd : ∀ i j, Commute (d i) (d j))
    (hHa : ∀ l i j, Commute (H l) (a i j))
    (hH0a : ∀ i j, Commute H0 (a i j)) :
    ActualModelCommutatorWords.commutator (modelFirstOrder d H H0) (modelSecondOrder d a B C) =
      secondBaseWords d H a B + firstBaseWords d H H0 a B C + zeroBaseWords d H H0 a B C := by
  exact ActualModelCommutatorWords.first_second_order_commutator_words
    (A := Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) d H H0 a B C hd hHa hH0a

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
