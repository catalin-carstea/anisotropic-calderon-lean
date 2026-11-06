import Calderon.MetricSmooth
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Topology

/-! Runge geometry in R3. -/
set_option autoImplicit false
noncomputable section
open Set Metric
namespace OAI.AnisotropicCalderon.SourceJet

theorem isConnected_closedBall_sdiff_closedBall
    (p : R3) (r R : ℝ) (hr : 0 ≤ r) (hRoom : ‖p‖ + r < R) :
    IsConnected (closedBall (0 : R3) R \ closedBall p r) := by
  let t : ℝ := (r + R - ‖p‖) / 2
  have hrt : r < t := by dsimp only [t]; linarith
  have htR : ‖p‖ + t < R := by dsimp only [t]; linarith
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  have hDim : 1 < Module.rank ℝ R3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [R3, finrank_euclideanSpace]
  have hSphere : IsConnected (sphere p t) :=
    (isPathConnected_sphere hDim p ht.le).isConnected
  have hSphereSub : sphere p t ⊆ closedBall (0 : R3) R \ closedBall p r := by
    intro z hz
    have hd : ‖z-p‖ = t := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hUpper := norm_le_norm_sub_add z p
    refine ⟨?_,?_⟩
    · rw [mem_closedBall,dist_zero_right]
      linarith
    · rw [mem_closedBall,dist_eq_norm]
      linarith
  obtain ⟨b,hb⟩ := hSphere.nonempty
  refine ⟨⟨b,hSphereSub hb⟩,?_⟩
  apply isPreconnected_of_forall b
  intro x hx
  have hd : r < ‖x-p‖ := by
    simpa only [mem_closedBall,dist_eq_norm,not_le] using hx.2
  have hd0 : 0 < ‖x-p‖ := lt_of_le_of_lt hr hd
  let z : R3 := p + (t / ‖x-p‖) • (x-p)
  have hzNorm : ‖z-p‖ = t := by
    dsimp only [z]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ht hd0)]
    exact div_mul_cancel₀ t hd0.ne'
  have hzSphere : z ∈ sphere p t := by
    simpa only [mem_sphere,dist_eq_norm] using hzNorm
  have hzOuter : z ∈ closedBall (0 : R3) R := (hSphereSub hzSphere).1
  have hSeg : segment ℝ x z ⊆ closedBall (0 : R3) R \ closedBall p r := by
    intro w hw
    refine ⟨(convex_closedBall (0 : R3) R).segment_subset hx.1 hzOuter hw,?_⟩
    rw [segment_eq_image] at hw
    obtain ⟨θ,hθ,rfl⟩ := hw
    have hc : 0 ≤ (1-θ)+θ*(t/‖x-p‖) :=
      add_nonneg (sub_nonneg.mpr hθ.2) (mul_nonneg hθ.1 (div_nonneg ht.le hd0.le))
    have hVec : (1-θ) • x + θ • z - p =
        ((1-θ)+θ*(t/‖x-p‖)) • (x-p) := by
      dsimp only [z]
      module
    have hNorm : ‖(1-θ) • x + θ • z - p‖ = (1-θ)*‖x-p‖ + θ*t := by
      rw [hVec,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
      field_simp [hd0.ne']
      <;> ring
    have hCombo : r < (1-θ)*‖x-p‖ + θ*t := by
      have h := (convex_Ioi r) hd hrt (sub_nonneg.mpr hθ.2) hθ.1 (sub_add_cancel 1 θ)
      simpa only [smul_eq_mul,mem_Ioi] using h
    rw [mem_closedBall,dist_eq_norm,hNorm]
    exact not_le_of_gt hCombo
  refine ⟨sphere p t ∪ segment ℝ x z,?_,Or.inl hb,
    Or.inr (left_mem_segment ℝ x z),?_⟩
  · exact union_subset hSphereSub hSeg
  · exact hSphere.isPreconnected.union z hzSphere (right_mem_segment ℝ x z)
      (convex_segment x z).isPreconnected

end OAI.AnisotropicCalderon.SourceJet
#print axioms OAI.AnisotropicCalderon.SourceJet.isConnected_closedBall_sdiff_closedBall
