import Calderon.ActualNormalizedPrincipalH8InitialSmallness
import Calderon.ActualMixedKernelOneDensityTwoUniformBounds

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile ReferenceWeightedApproximation
  CoordinateBootstrapJets ActualScalarPrincipalAdjoint
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ActualNormalizedPrincipalH8InitialSmallness

/-- One spatial dilation gives the strict coefficient inequality at every
fixed positive original reference depth, uniformly in the softplus parameter. -/
theorem exists_positive_depth_strict_current_radius_bound
    (S : KnownSideSourceData) (L eps Rstar tmin : ℝ) (p : ℕ)
    (hL : 0 < L) (heps : 0 < eps) (hRstar : 0 < Rstar)
    (htmin : 0 < tmin) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧
      ∀ lam ∈ Icc (0 : ℝ) lam0, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        ∀ y ∈ cylinder, tmin ≤ referenceDepth L y →
          coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
            (eps / 2) * referenceRadius delta Rstar p L y := by
  let a := Rstar * tmin ^ p
  have ha : 0 < a := mul_pos hRstar (pow_pos htmin p)
  obtain ⟨lam0, hlam0, hlam01, hSmall⟩ :=
    exists_referenceNormalizedPrincipalDifference_coordinateH8_small
      S.g1 S.g2 S.g1_admissible S.g2_admissible S.g1_origin S.g2_origin
      L cylinder isCompact_native_center_cylinder ((eps / 2) * a)
      (mul_pos (by linarith) ha)
  refine ⟨lam0, hlam0, hlam01, ?_⟩
  intro lam hlam delta hdelta _hdelta1 y hy hDepth
  have hSoft : tmin ≤ softplus delta (referenceDepth L y) :=
    hDepth.trans (le_softplus delta (referenceDepth L y) hdelta)
  have hRadius : a ≤ referenceRadius delta Rstar p L y := by
    unfold referenceRadius
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ htmin.le hSoft p) hRstar.le
  calc
    coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y
        ≤ (eps / 2) * a := hSmall lam hlam y hy
    _ ≤ (eps / 2) * referenceRadius delta Rstar p L y :=
      mul_le_mul_of_nonneg_left hRadius (by linarith)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
