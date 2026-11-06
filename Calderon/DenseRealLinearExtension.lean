import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DenseRealLinearExtension
variable {E G F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma extendOfNorm_apply_dense (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] G)
    (hd : DenseRange e) (C : ℝ) (hb : ∀ a, ‖f a‖ ≤ C*‖e a‖) (a : E) :
    f.extendOfNorm e (e a) = f a := by
  exact LinearMap.extendOfNorm_eq hd ⟨C,hb⟩ a

lemma norm_extendOfNorm_apply_dense (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] G)
    (hd : DenseRange e) (C : ℝ) (hb : ∀ a, ‖f a‖ ≤ C*‖e a‖) (u : G) :
    ‖f.extendOfNorm e u‖ ≤ C*‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le hd C hb u

#print axioms extendOfNorm_apply_dense
#print axioms norm_extendOfNorm_apply_dense
end OAI.AnisotropicCalderon.DenseRealLinearExtension
