import Calderon.SequenceLpInheritedStructureData

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
SEQUENCE-LP-EXPLICIT-NATURAL-STRUCTURE-EXPANSION-v001.md. Explicit existing natural constructors, no replacement structures. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural
    {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    (p : ENNReal) [Fact (1 ≤ p)] :
    (lp.normedAddCommGroup (E := E) (p := p)).toAddCommGroup.toAddCommMonoid =
      AddSubmonoidClass.toAddCommMonoid (lp E p) := rfl

lemma sequenceLp_normedSpace_module_eq_natural
    {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (p : ENNReal) [Fact (1 ≤ p)] :
    (lp.instNormedSpace (𝕜 := ℝ) (E := E) (p := p)).toModule =
      lp.instModuleSubtypePreLpMemAddSubgroup (𝕜 := ℝ) (E := E) (p := p) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sequenceLp_normedSpace_module_eq_natural
