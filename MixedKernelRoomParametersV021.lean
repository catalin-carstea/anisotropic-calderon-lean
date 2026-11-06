import MixedKernelPhaseChartsV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

/-! R1–R7 (REPORT.md v020 §R, written before this code): the v002 fixed-data rooms,
the asymmetric support-box cutoff, `χ = 1` on the lifted closure of `O`, the
derivative-support dichotomy and the closed known-side cross gaps. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.PhaseCoordinates

/-- R1: the v002 parameters `R`, `l`, `e` (here `roomE`). -/
def roomR (a : ℝ) : ℝ := min (a / 4) 1
def roomL (a c κ : ℝ) : ℝ :=
  min (min (roomR a / 16) (c * roomR a ^ 2 / 72)) (min (1 / (16 * κ)) 1)
def roomE (a c κ : ℝ) : ℝ := κ * roomL a c κ ^ 2 / 64

theorem roomParams_spec_aux {a c κ R l ε : ℝ} (ha : 0 < a) (hc : 0 < c) (hκ : 0 < κ)
    (hRd : R = min (a / 4) 1)
    (hld : l = min (min (R / 16) (c * R ^ 2 / 72)) (min (1 / (16 * κ)) 1))
    (hεd : ε = κ * l ^ 2 / 64) :
    0 < R ∧ R ≤ a / 4 ∧ R ≤ 1 ∧ 0 < l ∧ l ≤ R / 16 ∧ l ≤ c * R ^ 2 / 72 ∧
    κ * l ≤ 1 / 16 ∧ l ≤ 1 ∧ 0 < ε ∧ ε ≤ l / 1024 ∧ 4 * ε < l ∧ 4 * ε < κ * l ^ 2 ∧
    2 * l ≤ c * R ^ 2 / 18 ∧ l + 4 * ε < R / 8 ∧ R / 8 < a ∧ κ * (l + 4 * ε) < 1 / 4 := by
  have hRpos : 0 < R := by
    rw [hRd]
    exact lt_min (div_pos ha (by norm_num)) one_pos
  have hRa : R ≤ a / 4 := by rw [hRd]; exact min_le_left _ _
  have hR1 : R ≤ 1 := by rw [hRd]; exact min_le_right _ _
  have hl1 : l ≤ R / 16 := by rw [hld]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hl2 : l ≤ c * R ^ 2 / 72 := by rw [hld]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hl3 : l ≤ 1 / (16 * κ) := by rw [hld]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hl4 : l ≤ 1 := by rw [hld]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hlpos : 0 < l := by
    rw [hld]
    exact lt_min (lt_min (div_pos hRpos (by norm_num))
      (div_pos (mul_pos hc (pow_pos hRpos 2)) (by norm_num)))
      (lt_min (div_pos one_pos (mul_pos (by norm_num) hκ)) one_pos)
  have hκl : κ * l ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hl3 hκ.le
    have e : κ * (1 / (16 * κ)) = 1 / 16 := by field_simp
    linarith
  have hεpos : 0 < ε := by
    rw [hεd]
    exact div_pos (mul_pos hκ (pow_pos hlpos 2)) (by norm_num)
  have hkll : κ * l ^ 2 ≤ l / 16 := by
    have h := mul_le_mul_of_nonneg_right hκl hlpos.le
    calc κ * l ^ 2 = κ * l * l := by ring
      _ ≤ 1 / 16 * l := h
      _ = l / 16 := by ring
  have hX : 0 < κ * l ^ 2 := mul_pos hκ (pow_pos hlpos 2)
  have hεl : ε ≤ l / 1024 := by rw [hεd]; linarith
  have h4l : 4 * ε < l := by linarith
  have h4k : 4 * ε < κ * l ^ 2 := by rw [hεd]; linarith
  have hcR : 0 ≤ c * R ^ 2 := mul_nonneg hc.le (sq_nonneg R)
  have h2l : 2 * l ≤ c * R ^ 2 / 18 := by linarith
  have hl8 : l + 4 * ε < R / 8 := by linarith
  have ha8 : R / 8 < a := by linarith
  have hκh : κ * (l + 4 * ε) < 1 / 4 := by
    have h := mul_lt_mul_of_pos_left (show l + 4 * ε < 2 * l by linarith) hκ
    linarith
  exact ⟨hRpos, hRa, hR1, hlpos, hl1, hl2, hκl, hl4, hεpos, hεl, h4l, h4k, h2l, hl8, ha8, hκh⟩

/-- R1 for the literal definitions. -/
theorem roomParams_spec {a c κ : ℝ} (ha : 0 < a) (hc : 0 < c) (hκ : 0 < κ) :
    0 < roomR a ∧ roomR a ≤ a / 4 ∧ roomR a ≤ 1 ∧ 0 < roomL a c κ ∧
    roomL a c κ ≤ roomR a / 16 ∧ roomL a c κ ≤ c * roomR a ^ 2 / 72 ∧
    κ * roomL a c κ ≤ 1 / 16 ∧ roomL a c κ ≤ 1 ∧ 0 < roomE a c κ ∧
    roomE a c κ ≤ roomL a c κ / 1024 ∧ 4 * roomE a c κ < roomL a c κ ∧
    4 * roomE a c κ < κ * roomL a c κ ^ 2 ∧ 2 * roomL a c κ ≤ c * roomR a ^ 2 / 18 ∧
    roomL a c κ + 4 * roomE a c κ < roomR a / 8 ∧ roomR a / 8 < a ∧
    κ * (roomL a c κ + 4 * roomE a c κ) < 1 / 4 :=
  roomParams_spec_aux ha hc hκ rfl rfl rfl

/-- R2: the height cutoff `alphaMinus * alphaPlus`. -/
def heightCut (l ε s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (-l + 17 * ε / 8)) / (3 * ε / 4)) *
    (1 - Real.smoothTransition ((s - (l + 17 * ε / 8)) / (3 * ε / 4)))

/-- R2: the lateral cutoff `beta`. -/
def lateralCut (R q : ℝ) : ℝ := 1 - Real.smoothTransition ((q - R ^ 2 / 4) / (5 * R ^ 2 / 16))

theorem contDiff_heightCut (l ε : ℝ) : ContDiff ℝ ∞ (heightCut l ε) := by
  unfold heightCut
  fun_prop

theorem contDiff_lateralCut (R : ℝ) : ContDiff ℝ ∞ (lateralCut R) := by
  unfold lateralCut
  fun_prop

theorem heightCut_ne_zero {l ε s : ℝ} (hε : 0 < ε) (h : heightCut l ε s ≠ 0) :
    -l + 17 * ε / 8 < s ∧ s < l + 23 * ε / 8 := by
  have hw : 0 < 3 * ε / 4 := by linarith
  unfold heightCut at h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  constructor
  · by_contra hs
    apply h1
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_le_iff₀ hw]
    linarith [not_lt.mp hs]
  · by_contra hs
    apply h2
    have hA : Real.smoothTransition ((s - (l + 17 * ε / 8)) / (3 * ε / 4)) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith [not_lt.mp hs])
    rw [hA, sub_self]

theorem heightCut_eq_one {l ε s : ℝ} (hε : 0 < ε) (h1 : -l + 23 * ε / 8 ≤ s)
    (h2 : s ≤ l + 17 * ε / 8) : heightCut l ε s = 1 := by
  have hw : 0 < 3 * ε / 4 := by linarith
  have hA : Real.smoothTransition ((s - (-l + 17 * ε / 8)) / (3 * ε / 4)) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith)
  have hB : Real.smoothTransition ((s - (l + 17 * ε / 8)) / (3 * ε / 4)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw]; linarith)
  unfold heightCut
  rw [hA, hB]
  ring

theorem lateralCut_ne_zero {R q : ℝ} (hR : 0 < R) (h : lateralCut R q ≠ 0) :
    q < 9 * R ^ 2 / 16 := by
  have hR2 := pow_pos hR 2
  have hw : 0 < 5 * R ^ 2 / 16 := by linarith
  by_contra hq
  apply h
  have hA : Real.smoothTransition ((q - R ^ 2 / 4) / (5 * R ^ 2 / 16)) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith [not_lt.mp hq])
  unfold lateralCut
  rw [hA, sub_self]

theorem lateralCut_eq_one {R q : ℝ} (hR : 0 < R) (h : q ≤ R ^ 2 / 4) : lateralCut R q = 1 := by
  have hR2 := pow_pos hR 2
  have hw : 0 < 5 * R ^ 2 / 16 := by linarith
  have hB : Real.smoothTransition ((q - R ^ 2 / 4) / (5 * R ^ 2 / 16)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw]; linarith)
  unfold lateralCut
  rw [hB, sub_zero]

end OAI.AnisotropicCalderon.PhaseCoordinates
end
end
