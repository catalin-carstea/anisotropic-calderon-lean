import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem clm_seminormedAddCommGroup_topologicalSpace_eq
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (U →L[ℝ] K)) := by
  rfl

theorem clm_seminormedAddCommGroup_addCommMonoid_eq
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (U →L[ℝ] K)) := by
  rfl

theorem clm_normedSpace_module_eq
    (U K : Type*) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toModule =
      (inferInstance : Module ℝ (U →L[ℝ] K)) := by
  rfl

theorem clm_normedAddCommGroup_seminormedAddCommGroup_eq
    (U K : Type*) [NormedAddCommGroup U] [NormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup =
      ContinuousLinearMap.toSeminormedAddCommGroup
        (E := U) (F := K) (σ₁₂ := RingHom.id ℝ) := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
