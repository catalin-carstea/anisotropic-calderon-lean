import Calderon.ActualReferenceRadiusInterpolationScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The exact manuscript choices n=3, eta=1/23, m=45 leave both
interpolation terms at least three-halves order for every jet j≤10. -/
theorem actual_interpolation_powers_le_three_halves
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (j : ℕ) (hj : j ≤ 10) :
    r ^ ((2 : ℝ) - ((j : ℝ) + 3/2)/23) ≤ r ^ (3/2 : ℝ) ∧
    r ^ (((45 : ℝ) - (j : ℝ))/23) ≤ r ^ (3/2 : ℝ) := by
  have hjR : (j : ℝ) ≤ 10 := by exact_mod_cast hj
  constructor
  · apply Real.rpow_le_rpow_of_exponent_ge hr hr1
    linarith
  · apply Real.rpow_le_rpow_of_exponent_ge hr hr1
    linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
