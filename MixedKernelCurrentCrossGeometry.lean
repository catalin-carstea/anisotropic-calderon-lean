import MixedKernelNativeProductAndBasis
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

/-- Explicit positive lower bound for the original defining function from its quadratic transform. -/
theorem positive_margin_of_quadratic_transform {K m a : ℝ}
    (hK : 0 ≤ K) (hm : 0 < m) (ha : 0 < a) (hbound : m ≤ a + K * a ^ 2 / 2) :
    0 < min 1 (m / (1 + K / 2)) ∧ min 1 (m / (1 + K / 2)) ≤ a := by
  have hden : 0 < 1 + K / 2 := by linarith
  refine ⟨lt_min zero_lt_one (div_pos hm hden), ?_⟩
  by_cases hlarge : 1 ≤ a
  · exact (min_le_left _ _).trans hlarge
  · have hasmall : a < 1 := lt_of_not_ge hlarge
    have hsq : a ^ 2 ≤ a := by nlinarith
    have hmul : K * a ^ 2 ≤ K * a := mul_le_mul_of_nonneg_left hsq hK
    have hlin : m ≤ (1 + K / 2) * a := by nlinarith
    exact (min_le_right _ _).trans ((div_le_iff₀ hden).mpr (by nlinarith))

/-- The exact closed top/lateral collar lies inside the exact closed room. -/
theorem closed_native_collar_subset_closedD {K : Type*} [NormedAddCommGroup K]
    {l ε R : ℝ} (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R :
      Set (ℝ × K)) ⊆ PhaseCoordinates.closedD l ε R := by
  rintro z (hz | hz)
  · exact PhaseCoordinates.roomD_subset_closedD
      (PhaseCoordinates.closedStop_subset_roomD hε hl hR hz)
  · exact PhaseCoordinates.roomD_subset_closedD
      (PhaseCoordinates.closedSlat_subset_roomD hε hl hR hz)

/-- Both actual closed cross pieces have one strictly positive margin in the CURRENT side. -/
theorem closed_native_cross_positive_margin {K1 K2 : Type*}
    [NormedAddCommGroup K1] [NormedAddCommGroup K2]
    (e1 : OpenPartialHomeomorph R3 (ℝ × K1))
    (e2 : OpenPartialHomeomorph R3 (ℝ × K2))
    {θ1 θ2 : R3 → ℝ} {P1 : R3 → K1} {P2 : R3 → K2} {p1 p2 : R3}
    (he1 : ∀ x, e1 x = (θ1 x, P1 (x - p1)))
    (he2 : ∀ y, e2 y = (θ2 y, P2 (y - p2)))
    (hP1 : ∀ v, ‖P1 v‖ ≤ ‖v‖) (hP2 : ∀ v, ‖P2 v‖ ≤ ‖v‖)
    {c l ε R K : ℝ} (hc : 0 < c) (hε : 0 < ε) (hl : 4 * ε < l)
    (hR : 0 < R) (hK : 0 ≤ K) (h2l : 2 * l ≤ c * R ^ 2 / 18)
    (hD1t : PhaseCoordinates.closedD l ε R ⊆ e1.target)
    (hD2t : PhaseCoordinates.closedD l ε R ⊆ e2.target)
    (rho : R3 × R3 → ℝ)
    (hgap : ∀ x ∈ e1.symm '' PhaseCoordinates.closedD l ε R,
      ∀ y ∈ e2.symm '' PhaseCoordinates.closedD l ε R,
      θ1 x + θ2 y + c * (‖x - p1‖ ^ 2 + ‖y - p2‖ ^ 2) ≤
        rho (x,y) + K * rho (x,y) ^ 2 / 2)
    (hside : ∀ x ∈ e1.symm '' PhaseCoordinates.closedD l ε R,
      ∀ y ∈ e2.symm '' PhaseCoordinates.closedD l ε R,
      0 < rho (x,y) + K * rho (x,y) ^ 2 / 2 ↔ 0 < rho (x,y)) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈
      (e1.symm '' PhaseCoordinates.closedD l ε R) ×ˢ
        (e2.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R)) ∪
      (e1.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R)) ×ˢ
        (e2.symm '' PhaseCoordinates.closedD l ε R), η ≤ rho z := by
  let m : ℝ := min (ε / 2) (c * R ^ 2 / 18)
  have hm : 0 < m := lt_min (half_pos hε) (by positivity)
  have hC1 : e1.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R) ⊆
      e1.symm '' PhaseCoordinates.closedD l ε R :=
    Set.image_mono (closed_native_collar_subset_closedD hε hl hR)
  have hC2 : e2.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R) ⊆
      e2.symm '' PhaseCoordinates.closedD l ε R :=
    Set.image_mono (closed_native_collar_subset_closedD hε hl hR)
  have hC1t := (closed_native_collar_subset_closedD (K := K1) hε hl hR).trans hD1t
  have hC2t := (closed_native_collar_subset_closedD (K := K2) hε hl hR).trans hD2t
  have hden : 0 < 1 + K / 2 := by linarith
  refine ⟨min 1 (m / (1 + K / 2)), lt_min zero_lt_one (div_pos hm hden), ?_⟩
  rintro ⟨x,y⟩ (⟨hx,hy⟩ | ⟨hx,hy⟩)
  · have hyt := hC2 hy
    have hb : m ≤ rho (x,y) + K * rho (x,y) ^ 2 / 2 :=
      PhaseCoordinates.known_cross_gap_two_spaces e1 e2 he1 he2 hP2 hc hε hR h2l hD1t hC2t
        hx hy (hgap x hx y hyt)
    have hp : 0 < rho (x,y) := (hside x hx y hyt).mp (hm.trans_le hb)
    exact (positive_margin_of_quadratic_transform hK hm hp hb).2
  · have hxt := hC1 hx
    have hswapped : θ2 y + θ1 x + c * (‖y - p2‖ ^ 2 + ‖x - p1‖ ^ 2) ≤
        rho (x,y) + K * rho (x,y) ^ 2 / 2 := by
      have h := hgap x hxt y hy
      linarith
    have hb : m ≤ rho (x,y) + K * rho (x,y) ^ 2 / 2 :=
      PhaseCoordinates.known_cross_gap_two_spaces e2 e1 he2 he1 hP1 hc hε hR h2l hD2t hC1t
        hy hx hswapped
    have hp : 0 < rho (x,y) := (hside x hxt y hy).mp (hm.trans_le hb)
    exact (positive_margin_of_quadratic_transform hK hm hp hb).2

/-- Actual product localization for the product max metric, with no coordinate convention change. -/
theorem product_closed_rooms_subset_closedBall {A B : Set R3} {p1 p2 : R3} {r : ℝ}
    (hA : A ⊆ Metric.closedBall p1 r) (hB : B ⊆ Metric.closedBall p2 r) :
    A ×ˢ B ⊆ Metric.closedBall (p1,p2) r := by
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  rw [Metric.mem_closedBall, Prod.dist_eq]
  exact max_le (Metric.mem_closedBall.mp (hA hx)) (Metric.mem_closedBall.mp (hB hy))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
