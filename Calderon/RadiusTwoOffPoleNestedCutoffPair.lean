import Calderon.RadiusTwoNativeSourceFoundation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Full EXPANSION.json precedes this actual nested compact cutoff construction. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem exists_radiusTwo_offpole_nested_cutoff_pair
    (p x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ {p}) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η χ : 𝓓(radiusTwoOpens, ℝ),
      (∀ z ∈ ball x ε, η z = 1) ∧
      (∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1) ∧
      tsupport (χ : R3 → ℝ) ⊆ (radiusTwoOpens : Set R3) \ {p} ∧
      tsupport (η : R3 → ℝ) ⊆ tsupport (χ : R3 → ℝ) ∧
      ball x ε ⊆ (radiusTwoOpens : Set R3) \ {p} := by
  have hNOpen : IsOpen (radiusTwoOpens : Set R3) := by
    change IsOpen (ball (0 : R3) 2)
    exact isOpen_ball
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {p}) :=
    IsOpen.sdiff hNOpen isClosed_singleton
  obtain ⟨r,hr,hRoom⟩ : ∃ r : ℝ, 0 < r ∧
      closedBall x r ⊆ (radiusTwoOpens : Set R3) \ {p} :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hOpen.mem_nhds hx)
  let ηB : ContDiffBump x := ⟨r/4,r/2,by linarith,by linarith⟩
  let χB : ContDiffBump x := ⟨r/2,3*r/4,by linarith,by linarith⟩
  have hηSupp : tsupport (ηB : R3 → ℝ) = closedBall x (r/2) := ηB.tsupport_eq
  have hχSupp : tsupport (χB : R3 → ℝ) = closedBall x (3*r/4) := χB.tsupport_eq
  have hηRoom : tsupport (ηB : R3 → ℝ) ⊆ closedBall x r := by
    rw [hηSupp]
    exact closedBall_subset_closedBall (by linarith)
  have hχRoom : tsupport (χB : R3 → ℝ) ⊆ closedBall x r := by
    rw [hχSupp]
    exact closedBall_subset_closedBall (by linarith)
  let η : 𝓓(radiusTwoOpens, ℝ) :=
    ⟨ηB,ηB.contDiff,ηB.hasCompactSupport,fun z hz => (hRoom (hηRoom hz)).1⟩
  let χ : 𝓓(radiusTwoOpens, ℝ) :=
    ⟨χB,χB.contDiff,χB.hasCompactSupport,fun z hz => (hRoom (hχRoom hz)).1⟩
  refine ⟨r/4,by linarith,η,χ,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact ηB.one_of_mem_closedBall (ball_subset_closedBall hz)
  · intro z hz
    apply χB.one_of_mem_closedBall
    change z ∈ tsupport (ηB : R3 → ℝ) at hz
    rw [hηSupp] at hz
    change z ∈ closedBall x (r/2)
    exact hz
  · intro z hz
    exact hRoom (hχRoom hz)
  · change tsupport (ηB : R3 → ℝ) ⊆ tsupport (χB : R3 → ℝ)
    rw [hηSupp,hχSupp]
    exact closedBall_subset_closedBall (by linarith)
  · intro z hz
    exact hRoom ((closedBall_subset_closedBall (by linarith : r/4 ≤ r))
      (ball_subset_closedBall hz))

end OAI.AnisotropicCalderon.ExteriorSource
