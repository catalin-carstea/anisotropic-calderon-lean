import Calderon.ActualMixedKernelOneDensityTwoUniformBounds
import MixedKernelCylinderBoundary

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile

/-- The exact middle set from the shrinking-balls source is compactly inside
the fixed original cylinder, with the depth threshold chosen before dilation. -/
theorem exists_actual_middle_compact_interior_buffer
    (L : ℝ) (hL : 0 < L) :
    ∃ tb : ℝ, 0 < tb ∧ 3 * tb < depthPrimitive L (1/8) (1/4) ∧
      let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
        referenceDepth L y ≤ 2 * tb}
      IsCompact K ∧ K ⊆ interior cylinder := by
  let tq := depthPrimitive L (1/8) (1/4)
  have htq : 0 < tq := depthPrimitive_quarter_pos L hL
  let tb := tq / 4
  have htb : 0 < tb := by dsimp [tb]; positivity
  have hthree : 3 * tb < tq := by dsimp [tb]; linarith
  refine ⟨tb, htb, by simpa only [tq] using hthree, ?_⟩
  dsimp
  have hClosed : IsClosed {y : R3 | -(1/2 : ℝ) ≤ y 2 ∧
      referenceDepth L y ≤ 2 * tb} := by
    change IsClosed ({y : R3 | -(1/2 : ℝ) ≤ y 2} ∩
      {y : R3 | referenceDepth L y ≤ 2 * tb})
    exact (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (contDiff_referenceDepth L).continuous continuous_const)
  constructor
  · change IsCompact (cylinder ∩ {y : R3 | -(1/2 : ℝ) ≤ y 2 ∧
      referenceDepth L y ≤ 2 * tb})
    exact isCompact_native_center_cylinder.inter_right hClosed
  · intro y hy
    obtain ⟨hyC,hyLower,hyDepth⟩ := hy
    have hDepthQuarter : referenceDepth L y < tq := by
      have h2tb : 2 * tb < tq := by linarith
      exact hyDepth.trans_lt h2tb
    have hCoord : referenceCoordinateDepth y < (1/4 : ℝ) := by
      by_contra hnot
      have hCoordLower : (1/4 : ℝ) ≤ referenceCoordinateDepth y := le_of_not_gt hnot
      have hDepthLower : tq ≤ referenceDepth L y :=
        (depthPrimitive_strictMono L (1/8) hL).monotone hCoordLower
      exact (not_le_of_gt hDepthQuarter) hDepthLower
    have hRadial : y 0 ^ 2 + y 1 ^ 2 < 1 := by
      unfold referenceCoordinateDepth at hCoord
      nlinarith only [hCoord, hyLower]
    have hBelow : (-1 : ℝ) < y 2 := by linarith
    have hAbove : y 2 < 1 := by
      unfold referenceCoordinateDepth at hCoord
      nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact mem_interior_cylinder_of_strict y hRadial hBelow hAbove

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
