import Calderon.ParametricSobolevForm

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Joint continuity of the actual coefficient form in its L-infinity coefficient and first
Sobolev argument, stated over the same generic binders as `coefficientFormL`. -/
theorem continuous_coefficientFormL_uncurry
    {X J V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure X) (i : V →L[ℝ] Lp J 2 mu) :
    Continuous (fun p : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu × V =>
      coefficientFormL mu i p.1 p.2) := by
  have hCoeff : Continuous (fun p : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu × V =>
      coefficientFormL mu i p.1) :=
    (coefficientFormL mu i).continuous.comp continuous_fst
  exact hCoeff.clm_apply continuous_snd

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_coefficientFormL_uncurry
