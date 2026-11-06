import Calderon.ParametricSobolevForm

/-! EXPANSION.json precedes the typed scalar evaluation primitive. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {X J V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]

theorem coefficientFormL_apply_apply (μ : Measure X)
    (i : V →L[ℝ] Lp J 2 μ)
    (C : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ μ) (u v : V) :
    coefficientFormL μ i C u v = TauCeti.lpBilinearForm μ C (i u) (i v) := by
  have hEvaluation : coefficientFormL μ i C u v =
      (TauCeti.lpBilinearForm μ C).bilinearComp i i u v :=
    congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ => B u v) (coefficientFormL_apply μ i C)
  exact hEvaluation.trans (ContinuousLinearMap.bilinearComp_apply (TauCeti.lpBilinearForm μ C) i i u v)

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientFormL_apply_apply
