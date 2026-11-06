import Mathlib.Analysis.Normed.Operator.NormedSpace
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
/-! Full upfront EXPANSION-v001.json precedes this source. All equalities retain
exact original Mathlib product norm, algebra, and topology constructors. -/

theorem prod_normedAddCommGroup_seminormedAddCommGroup_eq
    (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    (Prod.normedAddCommGroup (E := E) (F := F)).toSeminormedAddCommGroup =
      Prod.seminormedAddCommGroup (E := E) (F := F) := by
  rfl

theorem prod_seminormedAddCommGroup_addCommMonoid_eq
    (E F : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] :
    (Prod.seminormedAddCommGroup (E := E) (F := F)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (E × F)) := by
  rfl

theorem prod_normedSpace_module_eq
    (E F : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] :
    (Prod.normedSpace (𝕜 := ℝ) (E := E) (F := F)).toModule =
      (inferInstance : Module ℝ (E × F)) := by
  rfl

theorem prod_seminormedAddCommGroup_topologicalSpace_eq
    (E F : Type*) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] :
    (Prod.seminormedAddCommGroup (E := E) (F := F)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (E × F)) := by
  rfl

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.prod_normedAddCommGroup_seminormedAddCommGroup_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.prod_seminormedAddCommGroup_addCommMonoid_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.prod_normedSpace_module_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.prod_seminormedAddCommGroup_topologicalSpace_eq
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
