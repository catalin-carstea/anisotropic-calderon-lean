import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.LinearIsometry
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.InnerIsometryOperatorEvaluation
/-! Full upfront EXPANSION-PARTITION-v004.json. Abstract scalar evaluation;
no actual sphere equivalence, carrier cast, or adjunction premise is used. -/
lemma innerSL_linear_isometry_equiv_eval_comp_apply
    {X U V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (Z : V ≃ₗᵢ[ℝ] W) (a : W) (g : U) (P : X →L[ℝ] (U →L[ℝ] V)) (x : X) :
    ((innerSL ℝ a).comp (Z.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.apply ℝ V g).comp P))) x = ⟪a,Z (P x g)⟫_ℝ := by
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    innerSL_apply_apply]
#print axioms OAI.AnisotropicCalderon.InnerIsometryOperatorEvaluation.innerSL_linear_isometry_equiv_eval_comp_apply
end OAI.AnisotropicCalderon.InnerIsometryOperatorEvaluation
