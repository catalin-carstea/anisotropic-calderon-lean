import Calderon.NormalizedPrincipalMetricSmooth

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorAffineMetricNormalization

/-- Coefficient normalization at an actual exterior unit base point.
This is g(e+2x), not an assertion of original-pair equality at zero or of energy transport. -/
def exteriorAffineNormalizedMetric (g : MatrixField) (e : R3) : MatrixField :=
  fun x => g (e+(2 : ℝ) • x)

theorem isAdmissibleMetric_exteriorAffineNormalizedMetric
    (g : MatrixField) (hg : IsAdmissibleMetric g) (e : R3) (he : ‖e‖=1) :
    IsAdmissibleMetric (exteriorAffineNormalizedMetric g e) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    exact (hg.smooth i j).comp
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => e)).add
        ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul contDiff_id))
  · intro x
    exact hg.posDef (e+(2 : ℝ) • x)
  · intro x hx
    have ht := norm_sub_le (e+(2 : ℝ) • x) e
    have hs : (e+(2 : ℝ) • x)-e=(2 : ℝ) • x := by abel
    rw [hs,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),he] at ht
    exact hg.euclidean_exterior (e+(2 : ℝ) • x) (by linarith)

theorem exteriorAffineNormalizedMetric_zero_eq_one
    (g : MatrixField) (hg : IsAdmissibleMetric g) (e : R3) (he : ‖e‖=1) :
    exteriorAffineNormalizedMetric g e 0=1 := by
  change g (e+(2 : ℝ) • (0 : R3))=1
  rw [smul_zero,add_zero]
  exact hg.euclidean_exterior e (by rw [he])

end OAI.AnisotropicCalderon.ExteriorAffineMetricNormalization
