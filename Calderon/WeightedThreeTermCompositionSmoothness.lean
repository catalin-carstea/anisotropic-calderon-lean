import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma contDiffAt_smul_add_smul_add_smul_comp
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : E} {T : E → F} {A B C : F → V} {a b c : E → ℝ}
    (hT : ContDiffAt ℝ ∞ T x)
    (hA : ContDiffAt ℝ ∞ A (T x)) (hB : ContDiffAt ℝ ∞ B (T x))
    (hC : ContDiffAt ℝ ∞ C (T x))
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x)
    (hc : ContDiffAt ℝ ∞ c x) :
    ContDiffAt ℝ ∞ (fun y => (a y • A (T y) + b y • B (T y)) + c y • C (T y)) x := by
  exact ((ha.smul (hA.comp x hT)).add (hb.smul (hB.comp x hT))).add
    (hc.smul (hC.comp x hT))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_smul_add_smul_add_smul_comp
