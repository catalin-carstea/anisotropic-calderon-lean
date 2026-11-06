import MixedKernelNativeProductAndBasis
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- The original defining function has its prescribed first jet, with an actual quadratic remainder. -/
theorem exists_original_separating_taylor (S : KnownSideSourceData) :
    ∃ M r : ℝ, 0 ≤ M ∧ 0 < r ∧ ∀ z ∈ Metric.ball (0 : R3) r,
      |S.separating_function z - z 2| ≤ M * ‖z‖^2 := by
  have hcd : ContDiffAt ℝ 2 S.separating_function (0 : R3) :=
    (S.separating_function_smooth.contDiffAt
      (S.coordinateRoom_open.mem_nhds S.origin_mem)).of_le (by simp)
  obtain ⟨M,r,hM,hr,H⟩ := exists_first_order_taylor hcd
  refine ⟨M,r,hM,hr,fun z hz => ?_⟩
  simpa only [S.separating_function_zero, sub_zero, S.separating_function_normal] using H z hz

/-- One ceiling gives room membership and the quantitative normalized planar error on a whole bounded set. -/
theorem exists_uniform_scaled_separating_error (S : KnownSideSourceData)
    (B eta : ℝ) (hB : 0 < B) (heta : 0 < eta) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ x : R3, ‖x‖ ≤ B → lam • x ∈ S.coordinateRoom ∧
        |S.separating_function (lam • x) - lam * x 2| ≤ lam * eta / 2 ∧
        (x 2 ≤ -eta → lam • x ∈ S.W) := by
  obtain ⟨M,r,hM,hr,H⟩ := exists_original_separating_taylor S
  obtain ⟨a,ha,hball,hW⟩ := S.one_sided_room
  let b := B+1
  have hb : 0 < b := by dsimp [b]; linarith
  have hBb : B < b := by dsimp [b]; linarith
  let lam0 := min (min r a / (2*b)) (eta/(2*(M+1)*b^2))
  have hden : 0 < 2*(M+1)*b^2 := by positivity
  have hlam0 : 0 < lam0 := lt_min (div_pos (lt_min hr ha) (by positivity)) (div_pos heta hden)
  refine ⟨lam0,hlam0,fun lam hlam hsmall x hx => ?_⟩
  have hroomBound : lam*(2*b) ≤ min r a :=
    (le_div_iff₀ (by positivity : (0:ℝ)<2*b)).mp (hsmall.trans (min_le_left _ _))
  have herrBound : lam*(2*(M+1)*b^2) ≤ eta :=
    (le_div_iff₀ hden).mp (hsmall.trans (min_le_right _ _))
  have hnorm : ‖lam • x‖ = lam * ‖x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hlam]
  have hnormb : ‖lam • x‖ ≤ lam*b := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hx.trans hBb.le) hlam.le
  have hlb : 0 < lam*b := mul_pos hlam hb
  have hzr : lam • x ∈ Metric.ball (0 : R3) r := by
    rw [Metric.mem_ball,dist_zero_right]
    have hmin := min_le_left r a
    nlinarith
  have hza : lam • x ∈ Metric.ball (0 : R3) a := by
    rw [Metric.mem_ball,dist_zero_right]
    have hmin := min_le_right r a
    nlinarith
  have hnormsq : ‖lam • x‖^2 ≤ (lam*b)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hlb.le).mpr hnormb
  have hMbound : M*(lam*b)^2 ≤ lam*eta/2 := by
    have hM1 : M ≤ M+1 := by linarith
    have hh := mul_le_mul_of_nonneg_left herrBound hlam.le
    have hm := mul_le_mul_of_nonneg_right hM1 (sq_nonneg (lam*b))
    nlinarith
  have he : |S.separating_function (lam • x)-lam*x 2| ≤ lam*eta/2 := by
    have ht := H (lam • x) hzr
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      ht.trans ((mul_le_mul_of_nonneg_left hnormsq hM).trans hMbound)
  refine ⟨hball hza,he,fun hheight => ?_⟩
  apply hW
  refine ⟨hza,?_⟩
  have hupper := (abs_le.mp he).2
  have hscaled := mul_le_mul_of_nonneg_left hheight hlam.le
  have hpos := mul_pos hlam heta
  nlinarith

/-- Every bounded strict lower strip lies in the literal original known side for all sufficiently small dilations. -/
theorem exists_uniform_scaled_lower_strip (S : KnownSideSourceData)
    (B eta : ℝ) (hB : 0 < B) (heta : 0 < eta) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ x : R3, ‖x‖ ≤ B → x 2 ≤ -eta → lam • x ∈ S.W := by
  obtain ⟨lam0,hpos,H⟩ := exists_uniform_scaled_separating_error S B eta hB heta
  exact ⟨lam0,hpos,fun lam hlam hsmall x hx hh => (H lam hlam hsmall x hx).2.2 hh⟩

/-- The same ceiling handles both original lower-cross pieces on the whole bounded separated range. -/
theorem exists_uniform_original_lower_cross (S : KnownSideSourceData)
    (B eta : ℝ) (hB : 0 < B) (heta : 0 < eta) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
      ∀ v : R3 × R3, ‖v.1‖ ≤ B → ‖v.2‖ ≤ B → v.1 ≠ v.2 →
        (v.1 2 ≤ -eta ∨ v.2 2 ≤ -eta) → v ∈ initialCross S lam := by
  obtain ⟨lam0,hpos,H⟩ := exists_uniform_scaled_separating_error S B eta hB heta
  refine ⟨lam0,hpos,fun lam hlam hsmall v hx hy hne hheight => ?_⟩
  have h1 := H lam hlam hsmall v.1 hx
  have h2 := H lam hlam hsmall v.2 hy
  refine ⟨⟨h1.1,h2.1,hne⟩,?_⟩
  exact hheight.elim (fun hh => Or.inl (h1.2.2 hh)) (fun hh => Or.inr (h2.2.2 hh))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
