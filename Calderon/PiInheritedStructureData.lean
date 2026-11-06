import Mathlib.Analysis.Normed.Operator.NormedSpace
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
/-! Full upfront EXPANSION-v001.json precedes source. Exact original finite-Pi
structures only; no replacement of the sup norm or pointwise algebra. -/

theorem pi_normedAddCommGroup_seminormedAddCommGroup_eq
    {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, NormedAddCommGroup (G i)] :
    (Pi.normedAddCommGroup (G := G)).toSeminormedAddCommGroup =
      Pi.seminormedAddCommGroup (G := G) := by
  rfl

theorem pi_seminormedAddCommGroup_addCommMonoid_eq
    {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)] :
    (Pi.seminormedAddCommGroup (G := G)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (∀ i, G i)) := by
  rfl

theorem pi_normedSpace_module_eq
    {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, NormedSpace ℝ (G i)] :
    (Pi.normedSpace (𝕜 := ℝ) (E := G)).toModule =
      (inferInstance : Module ℝ (∀ i, G i)) := by
  rfl

theorem pi_seminormedAddCommGroup_topologicalSpace_eq
    {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)] :
    (Pi.seminormedAddCommGroup (G := G)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (∀ i, G i)) := by
  rfl

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.pi_normedAddCommGroup_seminormedAddCommGroup_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.pi_seminormedAddCommGroup_addCommMonoid_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.pi_normedSpace_module_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.pi_seminormedAddCommGroup_topologicalSpace_eq
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
