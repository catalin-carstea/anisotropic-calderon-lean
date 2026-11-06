import Calderon.ActualPhysicalDensityOperatorGermCongruence
import Calderon.ActualCommonRadiusPhysicalHalfGraph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
open SphereHarmonic

theorem exists_smooth_compact_fiveHalf_source_eq_germ_in_open_room
    (U:Set R3) (hU:IsOpen U) (y:R3) (hy:y∈U)
    (u:R3→SphereSobolev (5/2:ℝ)) (hu:ContDiff ℝ ∞ u):
    ∃ u0:R3→SphereSobolev (5/2:ℝ),ContDiff ℝ ∞ u0 ∧ HasCompactSupport u0 ∧
      tsupport u0⊆U ∧ u0=ᶠ[𝓝 y]u := by
  obtain ⟨e,he,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let f:ContDiffBump y := ⟨e/4,e/2,by positivity,by linarith⟩
  let u0:R3→SphereSobolev (5/2:ℝ) := fun z => f z • u z
  have hS:tsupport u0⊆tsupport (f:R3→ℝ) := tsupport_smul_subset_left _ _
  refine ⟨u0,f.contDiff.smul hu,f.hasCompactSupport.smul_right,?_,?_⟩
  · exact hS.trans (by rw [f.tsupport_eq];exact (closedBall_subset_ball (by dsimp only [f];linarith)).trans hBall)
  · filter_upwards [f.eventuallyEq_one] with z hz
    change f z • u z=u z
    rw [hz,Pi.one_apply,one_smul]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicCore
