import Calderon.NativeCoordinateOperatorBounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon
open EnergyBridge DirichletFamily

def coordinateExpansion {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : Fin 3 → V) : R3 →L[ℝ] V :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).smulRight (v i)

lemma coordinateExpansion_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : Fin 3 → V) (x : R3) :
    coordinateExpansion v x = ∑ i : Fin 3, x i • v i := by
  simp only [coordinateExpansion, sum_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj]

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.coordinateExpansion
#print axioms OAI.AnisotropicCalderon.coordinateExpansion_apply
