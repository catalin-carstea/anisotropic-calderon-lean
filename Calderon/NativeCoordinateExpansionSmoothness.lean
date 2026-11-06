import Calderon.NativeCoordinateExpansion
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped ContDiff BigOperators
namespace OAI.AnisotropicCalderon
open EnergyBridge DirichletFamily

lemma contDiffOn_coordinateExpansion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ∞ω} (Z : Set R3) (v : Fin 3 → R3 → V)
    (hv : ∀ i : Fin 3, ContDiffOn ℝ n (v i) Z) :
    ContDiffOn ℝ n (fun z => coordinateExpansion (fun i : Fin 3 => v i z)) Z := by
  dsimp only [coordinateExpansion]
  apply ContDiffOn.sum
  intro i _
  have hConst : ContDiffOn ℝ n
      (fun _ : R3 => (EuclideanSpace.proj i : R3 →L[ℝ] ℝ)) Z :=
    contDiffOn_const
  exact hConst.smulRight (hv i)

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.contDiffOn_coordinateExpansion
