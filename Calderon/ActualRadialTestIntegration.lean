import Calderon.NativeSmoothBallSobolev
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.RadialTestIntegration

/-! First actual ingredient of ball Green's identity. The upfront mathematical
expansion is EXPANSION-ball-Green-spectral-sharp-trace-v001.json. This module
proves a whole-space radial test identity only; it asserts no ball flux,
sharp boundary trace, or physical moving-sphere estimate. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A smooth radial scalar cutoff is an actual test function on the ambient space. -/
def radialNormSqTestFunction (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (R : ℝ) (hR : 0 < R) (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0) :
    𝓓((⊤ : Opens E), ℝ) where
  toFun := fun x => χ (‖x‖^2)
  contDiff' := hχ.comp (contDiff_norm_sq ℝ)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E) R)
    intro x hx
    have hnorm : R ≤ ‖x‖ := by
      have hn : ¬ ‖x‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using hx
      exact (lt_of_not_ge hn).le
    exact hχ0 _ (pow_le_pow_left₀ hR.le hnorm 2)
  tsupport_subset' := by intro x hx; trivial

/-- The literal directional derivative of the radial test function. -/
theorem lineDeriv_radialNormSqTestFunction (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (R : ℝ) (hR : 0 < R) (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0)
    (x v : E) :
    lineDeriv ℝ (radialNormSqTestFunction χ hχ R hR hχ0 : E → ℝ) x v =
      2 * deriv χ (‖x‖^2) * ⟪x,v⟫_ℝ := by
  have hd := ((hχ.differentiable (by simp) (‖x‖^2)).hasDerivAt).comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hl := (hd.hasLineDerivAt v).lineDeriv
  change lineDeriv ℝ (fun y : E => χ (‖y‖^2)) x v = _
  calc
    lineDeriv ℝ (fun y : E => χ (‖y‖^2)) x v =
        deriv χ (‖x‖^2) * (⟪x,v⟫_ℝ + ⟪x,v⟫_ℝ) := by
      simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul,
        two_smul, ContinuousLinearMap.add_apply, Function.comp_def] using hl
    _ = 2 * deriv χ (‖x‖^2) * ⟪x,v⟫_ℝ := by ring

/-- Exact radial directional integration by parts, with a genuine compactly
supported test function and the classical derivative of the actual datum. -/
theorem integral_radialNormSqTestFunction_fderiv (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (hR : 0 < R)
    (hχ0 : ∀ t : ℝ, R^2 ≤ t → χ t = 0)
    (u : E → ℝ) (hu : ContDiff ℝ 1 u) (v : E) :
    (∫ x : E, (2 * deriv χ (‖x‖^2) * ⟪x,v⟫_ℝ) * u x ∂μ) =
      -(∫ x : E, χ (‖x‖^2) * (fderiv ℝ u x v) ∂μ) := by
  have hdu : Continuous (fun x : E => fderiv ℝ u x v) :=
    (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hw : TauCeti.HasWeakLineDerivOn μ (⊤ : Opens E) u
      (fun x : E => fderiv ℝ u x v) v :=
    TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      (hu.continuous.continuousOn.locallyIntegrableOn MeasurableSet.univ)
      (hdu.continuousOn.locallyIntegrableOn MeasurableSet.univ)
      (fun x hx => (hu.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt v)
  have hi := hw.integral_lineDeriv_smul_eq_neg_integral_smul
    (radialNormSqTestFunction χ hχ R hR hχ0)
  simp only [lineDeriv_radialNormSqTestFunction, smul_eq_mul] at hi
  exact hi

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.radialNormSqTestFunction
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.lineDeriv_radialNormSqTestFunction
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_radialNormSqTestFunction_fderiv
