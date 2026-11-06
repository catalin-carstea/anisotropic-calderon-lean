import Calderon.ActualWeightedNativeFiveSourceMomentHelpers
import Calderon.ReferenceRadiusScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile CoordinateBootstrapJets NormalizedPrincipalMetric

/-- The original small-radius superlinear estimate and one-dilation large-radius
estimate give one strict half-bootstrap on the exact middle set. -/
theorem actual_middle_half_bootstrap_of_superlinear_and_one_dilation
    (S : KnownSideSourceData) (L lam delta Rstar eps C rho tb : ℝ) (p : ℕ)
    (hDelta : 0 < delta) (hRstar : 0 < Rstar)
    (hEps : 0 < eps) (hC : 0 ≤ C) (hRho : 0 < rho)
    (hChoice : C * rho ^ ((1 : ℝ)/2) ≤ eps/2) :
    let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
      referenceDepth L y ≤ 2 * tb}
    (∀ y ∈ K, referenceRadius delta Rstar p L y < rho →
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        C * (referenceRadius delta Rstar p L y) ^ (3/2 : ℝ)) →
    (∀ y ∈ K, rho ≤ referenceRadius delta Rstar p L y →
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        (eps/2) * rho) →
    ∀ y ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        (eps/2) * referenceRadius delta Rstar p L y := by
  dsimp
  intro hSmall hLarge y hy
  let r : ℝ := referenceRadius delta Rstar p L y
  have hr : 0 < r := referenceRadius_pos delta Rstar p L y hDelta hRstar
  by_cases hlt : r < rho
  · have hPow : r ^ ((1 : ℝ)/2) ≤ rho ^ ((1 : ℝ)/2) :=
      Real.rpow_le_rpow hr.le hlt.le (by norm_num)
    have hThree : r ^ (3/2 : ℝ) = r * r ^ ((1 : ℝ)/2) := by
      convert Real.rpow_add hr (1 : ℝ) (1/2 : ℝ) using 1 <;> norm_num
    calc
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y
          ≤ C * r ^ (3/2 : ℝ) := hSmall y hy hlt
      _ = (C * r ^ ((1 : ℝ)/2)) * r := by rw [hThree]; ring
      _ ≤ (C * rho ^ ((1 : ℝ)/2)) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hC) hr.le
      _ ≤ (eps/2) * r := mul_le_mul_of_nonneg_right hChoice hr.le
  · have hrhoLe : rho ≤ r := le_of_not_gt hlt
    calc
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y
          ≤ (eps/2) * rho := hLarge y hy hrhoLe
      _ ≤ (eps/2) * r := mul_le_mul_of_nonneg_left hrhoLe (by positivity)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
