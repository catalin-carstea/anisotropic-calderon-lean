import Calderon.RadiusTwoOffPoleDyadicCutoffChain
import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels
import Calderon.RadiusTwoFiniteRowCutoffSmoothness

set_option autoImplicit false
noncomputable section
open Set Metric Filter TopologicalSpace MeasureTheory
open scoped Distributions Topology ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem exists_radiusTwo_compactPole_dyadic_cutoff_room
    (P : Set R3) (hP : IsCompact P) (x : R3)
    (hx : x ∈ (radiusTwoOpens : Set R3) \ P) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : ℕ → 𝓓(radiusTwoOpens, ℝ),
      closedBall x r ⊆ (radiusTwoOpens : Set R3) \ P ∧
      (∀ j : ℕ, ∀ z ∈ ball x (r/2), η j z = 1) ∧
      (∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ closedBall x r) ∧
      (∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1) ∧
      (∀ p ∈ P, ∀ j : ℕ, p ∉ tsupport (η j : R3 → ℝ)) ∧
      ball x (r/2) ⊆ (radiusTwoOpens : Set R3) \ P := by
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ P) :=
    IsOpen.sdiff radiusTwoOpens.isOpen hP.isClosed
  obtain ⟨r, hr, hRoom⟩ : ∃ r : ℝ, 0 < r ∧
      closedBall x r ⊆ (radiusTwoOpens : Set R3) \ P :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hOpen.mem_nhds hx)
  have htPos (j : ℕ) : 0 < (1/2 : ℝ)^j := pow_pos (by norm_num) j
  have htLe (j : ℕ) : (1/2 : ℝ)^j ≤ 1 :=
    pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hRPos (j : ℕ) : 0 < r * (1/2 : ℝ)^j := mul_pos hr (htPos j)
  have hRLe (j : ℕ) : r * (1/2 : ℝ)^j ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (htLe j) hr.le
  let B (j : ℕ) : ContDiffBump x :=
    ⟨r-(r/2)*(1/2 : ℝ)^j, r-(r/4)*(1/2 : ℝ)^j,
      by nlinarith [hRLe j], by nlinarith [hRPos j]⟩
  have hSupp (j : ℕ) : tsupport (B j : R3 → ℝ) =
      closedBall x (r-(r/4)*(1/2 : ℝ)^j) := (B j).tsupport_eq
  have hBRoom (j : ℕ) : tsupport (B j : R3 → ℝ) ⊆ closedBall x r := by
    rw [hSupp]
    exact closedBall_subset_closedBall (by nlinarith [hRPos j])
  let η (j : ℕ) : 𝓓(radiusTwoOpens, ℝ) :=
    ⟨B j, (B j).contDiff, (B j).hasCompactSupport, fun z hz => (hRoom (hBRoom j hz)).1⟩
  refine ⟨r, hr, η, hRoom, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro p hp j hpSupp
    exact (hRoom (hBRoom j hpSupp)).2 hp
  · intro z hz
    exact hRoom ((closedBall_subset_closedBall (by linarith : r/2 ≤ r))
      (ball_subset_closedBall hz))

theorem exists_radiusTwo_compactPole_cutoff_row_smoothness
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (P : Set R3) (hP : IsCompact P) (x : R3)
    (hx : x ∈ (radiusTwoOpens : Set R3) \ P) :
    ∃ r : ℝ, 0 < r ∧ ∃ η : ℕ → 𝓓(radiusTwoOpens, ℝ),
      closedBall x r ⊆ (radiusTwoOpens : Set R3) \ P ∧
      (∀ j : ℕ, ∀ z ∈ ball x (r/2), η j z = 1) ∧
      (∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ closedBall x r) ∧
      (∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1) ∧
      (∀ p ∈ P, ∀ j : ℕ, p ∉ tsupport (η j : R3 → ℝ)) ∧
      ball x (r/2) ⊆ (radiusTwoOpens : Set R3) \ P ∧
      (∀ p : (radiusTwoOpens : Set R3), (p : R3) ∈ P →
        ContDiffOn ℝ ∞ (G p) (ball x (r/2))) ∧
      (∀ (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3)),
        (∀ i : Fin m, (p i : R3) ∈ P) → ∀ j : ℕ,
        ContDiffOn ℝ ∞ (fun z => η j z * ∑ i : Fin m, a i * G (p i) z)
          (radiusTwoOpens : Set R3) ∧
        ContDiffOn ℝ ∞ (fun z => η j ((2 : ℝ) • z) *
          ∑ i : Fin m, a i * G (p i) ((2 : ℝ) • z)) (ballOpens : Set R3)) := by
  have hRoom := exists_radiusTwo_compactPole_dyadic_cutoff_room P hP x hx
  rcases hRoom with ⟨r, hr, η, hClosed, hOne, hSupp, hNext, hAvoid, hSmall⟩
  have hSeparate := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  refine ⟨r, hr, η, hClosed, hOne, hSupp, hNext, hAvoid, hSmall, ?_, ?_⟩
  · intro p hp
    apply (hSeparate.2.1 p).mono
    intro y hy
    have hyRoom := hSmall hy
    refine ⟨hyRoom.1, ?_⟩
    intro hyPole
    have hyEq : y = (p : R3) := mem_singleton_iff.mp hyPole
    exact hyRoom.2 (hyEq.symm ▸ hp)
  · intro m a p hp j
    exact contDiffOn_radiusTwo_finiteRow_cutoff hreg hcalc g hg K G hData
      m a p (η j) (fun i => hAvoid (p i) (hp i) j)

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_compactPole_dyadic_cutoff_room
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_compactPole_cutoff_row_smoothness
