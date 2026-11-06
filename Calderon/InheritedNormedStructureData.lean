import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem real_nontriviallyNormedField_normedField_eq :
    (Real.denselyNormedField.toNontriviallyNormedField).toNormedField = Real.normedField := by
  rfl

theorem submodule_seminormedAddCommGroup_topologicalSpace_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.seminormedAddCommGroup s).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace s) := by
  rfl

theorem submodule_seminormedAddCommGroup_addCommMonoid_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.seminormedAddCommGroup s).toAddCommGroup.toAddCommMonoid =
      Submodule.addCommMonoid s := by
  rfl

theorem submodule_normedSpace_module_eq
    (V : Type*) [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.normedSpace (𝕜 := ℝ) s).toModule = Submodule.module s := by
  rfl

theorem submodule_normedAddCommGroup_seminormedAddCommGroup_eq
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Submodule ℝ V) :
    (Submodule.normedAddCommGroup s).toSeminormedAddCommGroup =
      Submodule.seminormedAddCommGroup s := by
  rfl

theorem normedAddCommGroup_ofSeparation_eq
    (V : Type*) [N : NormedAddCommGroup V]
    (h : ∀ v : V, ‖v‖ = 0 → v = 0) :
    @NormedAddCommGroup.ofSeparation V N.toSeminormedAddCommGroup h = N := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
