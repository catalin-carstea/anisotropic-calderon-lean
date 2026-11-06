import Calderon.ClmNaturalStructureData
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Inherited data only, with no replacement structures. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype
    {R V : Type*} [Ring R] [n : SeminormedAddCommGroup V] [Module R V]
    (s : Submodule R V) :
    (Submodule.seminormedAddCommGroup s).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      @instTopologicalSpaceSubtype V (fun v => v ∈ s)
        n.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := rfl

lemma submodule_seminormedAddCommGroup_addCommMonoid_eq_natural
    {R V : Type*} [Ring R] [SeminormedAddCommGroup V] [Module R V]
    (s : Submodule R V) :
    (Submodule.seminormedAddCommGroup s).toAddCommGroup.toAddCommMonoid =
      Submodule.addCommMonoid s := rfl

lemma submodule_seminormedAddCommGroup_addCommGroup_eq_normed
    {R V : Type*} [Ring R] [NormedAddCommGroup V] [Module R V]
    (s : Submodule R V) :
    (Submodule.seminormedAddCommGroup s).toAddCommGroup =
      (Submodule.normedAddCommGroup s).toAddCommGroup := rfl

lemma submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent
    {R V : Type*} [Ring R] [NormedAddCommGroup V] [Module R V]
    (s : Submodule R V) :
    (Submodule.normedAddCommGroup s).toSeminormedAddCommGroup =
      Submodule.seminormedAddCommGroup s := rfl

lemma real_semifield_semiring_eq_natural :
    (inferInstance : Semifield ℝ).toCommSemiring.toSemiring = Real.semiring := rfl

lemma real_seminormedRing_addCommGroup_eq_natural :
    (inferInstance : NonUnitalSeminormedRing ℝ).toSeminormedAddCommGroup.toAddCommGroup =
      Real.instAddCommGroup := rfl

lemma real_seminormedRing_pseudoMetricSpace_eq_natural :
    (inferInstance : NonUnitalSeminormedRing ℝ).toSeminormedAddCommGroup.toPseudoMetricSpace =
      Real.pseudoMetricSpace := rfl

lemma real_seminormedRing_addCommMonoid_eq_natural :
    (inferInstance : NonUnitalSeminormedRing ℝ).toSeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid =
      Real.semiring.toAddCommMonoid := rfl

lemma real_innerProductSpace_module_eq_natural :
    (inferInstance : InnerProductSpace ℝ ℝ).toNormedSpace.toModule =
      (Semiring.toModule : Module ℝ ℝ) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.submodule_seminormedAddCommGroup_topologicalSpace_eq_subtype
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.submodule_seminormedAddCommGroup_addCommMonoid_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.submodule_seminormedAddCommGroup_addCommGroup_eq_normed
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.submodule_normedAddCommGroup_seminormedAddCommGroup_eq_independent
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_semifield_semiring_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_seminormedRing_addCommGroup_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_seminormedRing_pseudoMetricSpace_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_seminormedRing_addCommMonoid_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_innerProductSpace_module_eq_natural
