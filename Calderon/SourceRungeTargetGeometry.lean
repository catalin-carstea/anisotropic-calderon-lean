import Calderon.BallComplementConnected
import Calderon.FixedExteriorSourceBall

/-! Full upfront expansion precedes the actual closed-source target geometry. -/
set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem exists_sourceRunge_target_radius
    (p : R3) (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ r : ℝ, 0 < r ∧
      closedBall p (2*r) ⊆ (radiusTwoOpens : Set R3) ∧
      Disjoint (closedBall fixedExteriorSourceCenter (1/8 : ℝ)) (closedBall p r) ∧
      IsConnected (closedBall (0 : R3) 2 \ closedBall p r) := by
  have hpNorm : ‖p‖ < 2 := mem_ball_zero_iff.mp hp
  have hDist : (1/8 : ℝ) < dist p fixedExteriorSourceCenter := by
    simpa only [mem_closedBall, not_le] using hSource
  let r : ℝ := min ((2-‖p‖)/4) ((dist p fixedExteriorSourceCenter-1/8)/4)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hr₁ : r ≤ (2-‖p‖)/4 := min_le_left _ _
  have hr₂ : r ≤ (dist p fixedExteriorSourceCenter-1/8)/4 := min_le_right _ _
  refine ⟨r,hr,?_,?_,?_⟩
  · intro x hx
    have hxDist : ‖x-p‖ ≤ 2*r := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hxNorm := norm_le_norm_sub_add x p
    have hxLt : ‖x‖ < 2 := by linarith
    exact mem_ball_zero_iff.mpr hxLt
  · apply Set.disjoint_left.mpr
    intro x hxW hxB
    have hxW' : dist x fixedExteriorSourceCenter ≤ (1/8 : ℝ) := hxW
    have hxB' : dist p x ≤ r := by simpa only [mem_closedBall, dist_comm] using hxB
    have htri := dist_triangle p x fixedExteriorSourceCenter
    linarith
  · exact SourceJet.isConnected_closedBall_sdiff_closedBall p r 2 hr.le (by linarith)

theorem not_mem_fixedExteriorSource_closedBall_of_norm_le_one
    (p : R3) (hp : ‖p‖ ≤ 1) :
    p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ) := by
  intro h
  have hgt := (fixedExteriorSource_closedBall_subset_annulus h).1
  linarith

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_sourceRunge_target_radius
#print axioms OAI.AnisotropicCalderon.ExteriorSource.not_mem_fixedExteriorSource_closedBall_of_norm_le_one
