import Calderon.LocalSmoothAmbientExtension
import Calderon.NativeSmoothMultiplicationTrace

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped ContDiff Topology Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

theorem exists_smoothData_sphere_reciprocal
    (m : SmoothData) (hpos : ∀ x : UnitSphere, 0 < m.1 x.1) :
    ∃ n : SmoothData, HasCompactSupport n.1 ∧
      (∀ x : UnitSphere, n.1 x.1 = (m.1 x.1)⁻¹) ∧
      (∀ x : R3, (‖x‖ ≤ (1/2 : ℝ) ∨ 2 ≤ ‖x‖) → n.1 x = 0) := by
  let K : Set R3 := Metric.sphere 0 1
  let S : Set R3 := m.1 ⁻¹' ({0}ᶜ : Set ℝ)
  have hK : IsCompact K := isCompact_sphere 0 1
  have hS : IsOpen S := isClosed_singleton.isOpen_compl.preimage m.2.continuous
  have hKS : K ⊆ S := by
    intro x hx
    change m.1 x ∉ ({0} : Set ℝ)
    exact (hpos ⟨x,hx⟩).ne'
  have hInv : ContDiffOn ℝ ∞ (fun x => (m.1 x)⁻¹) S := by
    apply m.2.contDiffOn.inv
    intro x hx
    exact hx
  obtain ⟨w,hwCompact,hw⟩ :=
    exists_smoothData_eq_near_compact K S hK hS hKS (fun x => (m.1 x)⁻¹) hInv
  let A : Set R3 := Metric.ball 0 2 \ Metric.closedBall 0 (1/2 : ℝ)
  have hA : IsOpen A := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hKA : K ⊆ A := by
    intro x hx
    have hxNorm : ‖x‖ = 1 := by
      simpa only [K,Metric.mem_sphere,dist_zero_right] using hx
    change dist x 0 < 2 ∧ ¬ dist x 0 ≤ (1/2 : ℝ)
    rw [dist_zero_right,hxNorm]
    constructor <;> norm_num
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hA Metric.isClosed_sphere hKA
  refine ⟨⟨fun x => χ x * w.1 x,hχ.mul w.2⟩,hwCompact.mul_left,?_,?_⟩
  · intro x
    have hχOne : χ x.1 = 1 := (hOne x.1).mp x.2
    have hwValue : w.1 x.1 = (m.1 x.1)⁻¹ := (hw x.1 x.2).eq_of_nhds
    change χ x.1 * w.1 x.1 = (m.1 x.1)⁻¹
    rw [hχOne,one_mul,hwValue]
  · intro x hx
    have hxA : x ∉ A := by
      change ¬ (dist x 0 < 2 ∧ ¬ dist x 0 ≤ (1/2 : ℝ))
      rw [dist_zero_right]
      intro h
      rcases hx with hx | hx
      · exact h.2 hx
      · exact (not_lt_of_ge hx) h.1
    have hχZero : χ x = 0 := by
      apply notMem_support.mp
      rw [hSupport]
      exact hxA
    change χ x * w.1 x = 0
    rw [hχZero,zero_mul]

theorem exists_bounded_smoothData_sphere_reciprocal
    (m : SmoothData) (hpos : ∀ x : UnitSphere, 0 < m.1 x.1) :
    ∃ (n : SmoothData) (N : ℝ), HasCompactSupport n.1 ∧ 0 ≤ N ∧
      (∀ x : UnitSphere, n.1 x.1 = (m.1 x.1)⁻¹) ∧
      (∀ x ∈ (ballOpens : Set R3), |n.1 x| ≤ N) ∧
      (∀ x ∈ (ballOpens : Set R3), ‖gradient n.1 x‖ ≤ N) := by
  obtain ⟨n,hnCompact,hn,_⟩ := exists_smoothData_sphere_reciprocal m hpos
  obtain ⟨N,hN,hnN,hgnN⟩ := exists_smooth_ball_multiplier_bound n
  exact ⟨n,N,hnCompact,hN,hn,hnN,hgnN⟩

end OAI.AnisotropicCalderon.DirichletFamily
