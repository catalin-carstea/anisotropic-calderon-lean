import Calderon.RadiusTwoOffPoleNestedCutoffRoom

/-! EXPANSION.json precedes one fixed dyadic cutoff sequence, valid for every finite order. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem exists_radiusTwo_offpole_dyadic_cutoff_chain
    (p x : R3) (hx : x ∈ (radiusTwoOpens : Set R3) \ {p}) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : Set R3, IsCompact C ∧
      C ⊆ (radiusTwoOpens : Set R3) \ {p} ∧
      ∃ η : ℕ → 𝓓(radiusTwoOpens, ℝ),
        (∀ j : ℕ, ∀ z ∈ ball x ε, η j z = 1) ∧
        (∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ C) ∧
        (∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1) ∧
        ball x ε ⊆ (radiusTwoOpens : Set R3) \ {p} := by
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {p}) :=
    IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
  obtain ⟨r,hr,hRoom⟩ : ∃ r : ℝ, 0 < r ∧
      closedBall x r ⊆ (radiusTwoOpens : Set R3) \ {p} :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hOpen.mem_nhds hx)
  have htPos (j : ℕ) : 0 < (1/2 : ℝ)^j := pow_pos (by norm_num) j
  have htLe (j : ℕ) : (1/2 : ℝ)^j ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hRPos (j : ℕ) : 0 < r * (1/2 : ℝ)^j := mul_pos hr (htPos j)
  have hRLe (j : ℕ) : r * (1/2 : ℝ)^j ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (htLe j) hr.le
  let B (j : ℕ) : ContDiffBump x :=
    ⟨r-(r/2)*(1/2 : ℝ)^j,r-(r/4)*(1/2 : ℝ)^j,
      by nlinarith [hRLe j],by nlinarith [hRPos j]⟩
  have hSupp (j : ℕ) : tsupport (B j : R3 → ℝ) =
      closedBall x (r-(r/4)*(1/2 : ℝ)^j) := (B j).tsupport_eq
  have hBRoom (j : ℕ) : tsupport (B j : R3 → ℝ) ⊆ closedBall x r := by
    rw [hSupp]
    exact closedBall_subset_closedBall (by nlinarith [hRPos j])
  let η (j : ℕ) : 𝓓(radiusTwoOpens, ℝ) :=
    ⟨B j,(B j).contDiff,(B j).hasCompactSupport,fun z hz => (hRoom (hBRoom j hz)).1⟩
  refine ⟨r/2,by linarith,closedBall x r,(isCompact_closedBall x r),hRoom,η,?_,?_,?_,?_⟩
  · intro j z hz
    apply (B j).one_of_mem_closedBall
    change z ∈ closedBall x (r-(r/2)*(1/2 : ℝ)^j)
    exact (closedBall_subset_closedBall (by nlinarith [hRLe j] :
      r/2 ≤ r-(r/2)*(1/2 : ℝ)^j)) (ball_subset_closedBall hz)
  · intro j z hz
    exact hBRoom j hz
  · intro j z hz
    apply (B (j+1)).one_of_mem_closedBall
    change z ∈ closedBall x (r-(r/2)*(1/2 : ℝ)^(j+1))
    change z ∈ tsupport (B j : R3 → ℝ) at hz
    rw [hSupp] at hz
    have hRadius : r-(r/2)*(1/2 : ℝ)^(j+1) = r-(r/4)*(1/2 : ℝ)^j := by
      rw [pow_succ]
      ring
    rw [hRadius]
    exact hz
  · intro z hz
    exact hRoom ((closedBall_subset_closedBall (by linarith : r/2 ≤ r))
      (ball_subset_closedBall hz))

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_offpole_dyadic_cutoff_chain
