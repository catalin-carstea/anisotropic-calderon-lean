import Mathlib.Analysis.Calculus.Deriv.Mul
set_option autoImplicit false
set_option maxSynthPendingDepth 10
namespace OAI.AnisotropicCalderon.OperatorCurveDerivative
lemma hasDerivAt_clm_fixed_argument_of_differentiableAt
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : ℝ → X →L[ℝ] Y) (x : ℝ) (hA : DifferentiableAt ℝ A x) (u : X) :
    HasDerivAt (fun θ : ℝ => A θ u) (deriv A x u) x := by
  simpa only [map_zero,add_zero] using hA.hasDerivAt.clm_apply (hasDerivAt_const x u)
end OAI.AnisotropicCalderon.OperatorCurveDerivative
#print axioms OAI.AnisotropicCalderon.OperatorCurveDerivative.hasDerivAt_clm_fixed_argument_of_differentiableAt
