import Calderon.NativeSobolevStageStructure

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
SEQUENCE-LP-INHERITED-STRUCTURE-EXPANSION-v001.md. Existing sequence-lp algebra projections, no replacement structures. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma sequenceLp_normedAddCommGroup_addCommMonoid_eq
    {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    (p : ENNReal) [Fact (1 ≤ p)] :
    (lp.normedAddCommGroup (E := E) (p := p)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (lp E p)) := rfl

lemma sequenceLp_normedSpace_module_eq
    {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (p : ENNReal) [Fact (1 ≤ p)] :
    (lp.instNormedSpace (𝕜 := ℝ) (E := E) (p := p)).toModule =
      (inferInstance : Module ℝ (lp E p)) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sequenceLp_normedAddCommGroup_addCommMonoid_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sequenceLp_normedSpace_module_eq
