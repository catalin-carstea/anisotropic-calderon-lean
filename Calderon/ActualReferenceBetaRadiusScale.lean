import Calderon.ActualHigherRadiusProfile
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualHigherRadiusProfile
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile ReferenceWeightedApproximation

/-- The actual logarithmic reference-radius beta is independent of the positive
multiplicative radius scale. -/
theorem actualReferenceBeta_eq_of_positive_scales
    (g : MatrixField) (L lam delta R1 R2 : ℝ) (p : ℕ) (x : R3)
    (hdelta : 0 < delta) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    actualReferenceBeta g L lam delta R1 p x =
      actualReferenceBeta g L lam delta R2 p x := by
  rw [actualReferenceBeta_eq g L lam delta R1 p hdelta hR1 x,
    actualReferenceBeta_eq g L lam delta R2 p hdelta hR2 x]

/-- Shrinking the positive radius scale preserves the genuine q=2 beta-radius
budget, including the separate normal-neighborhood radius ceiling. -/
theorem referenceRadius_beta_sq_mono_scale
    (g : MatrixField) (L lam delta R1 R2 : ℝ) (p : ℕ) (x : R3)
    (hdelta : 0 < delta) (hR1 : 0 < R1) (hR2 : 0 < R2) (hscale : R1 ≤ R2) :
    referenceRadius delta R1 p L x * (actualReferenceBeta g L lam delta R1 p x)^2 ≤
      referenceRadius delta R2 p L x * (actualReferenceBeta g L lam delta R2 p x)^2 ∧
    referenceRadius delta R1 p L x ≤ referenceRadius delta R2 p L x := by
  have hradius : referenceRadius delta R1 p L x ≤ referenceRadius delta R2 p L x := by
    unfold referenceRadius
    exact mul_le_mul_of_nonneg_right hscale
      (pow_nonneg (softplus_pos delta (referenceDepth L x) hdelta).le p)
  have hbeta := actualReferenceBeta_eq_of_positive_scales g L lam delta R1 R2 p x
    hdelta hR1 hR2
  constructor
  · rw [hbeta]
    exact mul_le_mul_of_nonneg_right hradius (sq_nonneg _)
  · exact hradius

end OAI.AnisotropicCalderon.ActualHigherRadiusProfile
