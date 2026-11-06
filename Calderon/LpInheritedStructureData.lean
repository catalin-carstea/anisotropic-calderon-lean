import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem lp_normedAddCommGroup_addCommMonoid_eq
    (A E : Type*) [MeasurableSpace A] [NormedAddCommGroup E]
    (p : ENNReal) [Fact (1 ≤ p)] (mu : Measure A) :
    (Lp.instNormedAddCommGroup (E := E) (p := p) (μ := mu)).toAddCommGroup.toAddCommMonoid =
      (inferInstance : AddCommMonoid (Lp E p mu)) := by
  rfl

theorem lp_normedSpace_module_eq
    (A E : Type*) [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ENNReal) [Fact (1 ≤ p)] (mu : Measure A) :
    (Lp.instNormedSpace (𝕜 := ℝ) (E := E) (p := p) (μ := mu)).toModule =
      (inferInstance : Module ℝ (Lp E p mu)) := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
