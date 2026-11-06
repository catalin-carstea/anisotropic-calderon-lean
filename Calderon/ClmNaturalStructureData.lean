import Calderon.ClmInheritedStructureData

/-! Explicit existing natural data, no replacement structures. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma clm_seminormedAddCommGroup_topologicalSpace_eq_natural
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      ContinuousLinearMap.topologicalSpace (E := U) (F := K) (σ := RingHom.id ℝ) := rfl

lemma clm_seminormedAddCommGroup_addCommMonoid_eq_natural
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toAddCommGroup.toAddCommMonoid =
      ContinuousLinearMap.addCommMonoid (M₁ := U) (M₂ := K) (σ₁₂ := RingHom.id ℝ) := rfl

lemma clm_normedSpace_module_eq_natural
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toModule =
      ContinuousLinearMap.module (S₃ := ℝ) (M := U) (M₃ := K) (σ₁₃ := RingHom.id ℝ) := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.clm_seminormedAddCommGroup_topologicalSpace_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.clm_seminormedAddCommGroup_addCommMonoid_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.clm_normedSpace_module_eq_natural
