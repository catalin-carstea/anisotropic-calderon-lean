import MixedKernelClosedCoarseSeed
import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelAnchoredKernelConstruction
import Calderon.CollaboratorUCPCarlemanOct17
import MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxHeartbeats 200000
/-! ## v053: Euclidean tube flat leading form (T1-T3 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- T1: the source cancellation `ω·(U₁-U₂) = b·U₂` (real and imaginary parts), with
`q = (ω+b)/‖ω+b‖²`; no smallness of `b`. -/
theorem tube_flat_normal_identities {ω v b w : R3} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hw : ⟪w, ω + b⟫_ℝ = 0) :
    ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ = ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ∧
      ⟪ω, v - w⟫_ℝ = ⟪b, w⟫_ℝ := by
  have hn2 : ‖ω + b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hωω : ⟪ω, ω⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  have hnn : ⟪ω + b, ω + b⟫_ℝ = ‖ω + b‖ ^ 2 := real_inner_self_eq_norm_sq _
  constructor
  · have hb : ⟪b, ω + b⟫_ℝ = ‖ω + b‖ ^ 2 - ⟪ω, ω + b⟫_ℝ := by
      have h := inner_add_left (𝕜 := ℝ) ω b (ω + b)
      rw [hnn] at h
      linarith
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hωω, hb, mul_sub,
      inv_mul_cancel₀ hn2]
  · have h1 : ⟪ω, v⟫_ℝ = ⟪v, ω⟫_ℝ := real_inner_comm v ω
    have h2 : ⟪ω, w⟫_ℝ = ⟪w, ω⟫_ℝ := real_inner_comm w ω
    have h3 : ⟪b, w⟫_ℝ = ⟪w, b⟫_ℝ := real_inner_comm w b
    have h4 := inner_add_right (𝕜 := ℝ) w ω b
    rw [inner_sub_right]
    linarith

/-- T2: for unit `ω`, `‖u‖² - (ω·u)² = ‖π_{ω⊥} u‖²`. -/
theorem unit_norm_sq_sub_inner_sq {ω : R3} (hω : ‖ω‖ = 1) (u : R3) :
    ‖u‖ ^ 2 - ⟪ω, u⟫_ℝ ^ 2 = ‖u - ⟪ω, u⟫_ℝ • ω‖ ^ 2 := by
  have h1 : ⟪u, ⟪ω, u⟫_ℝ • ω⟫_ℝ = ⟪ω, u⟫_ℝ * ⟪ω, u⟫_ℝ := by
    rw [inner_smul_right, real_inner_comm]
  have h2 : ‖⟪ω, u⟫_ℝ • ω‖ = |⟪ω, u⟫_ℝ| := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs]
  rw [norm_sub_sq_real, h1, h2, sq_abs]
  ring

/-- T3: the flat projected form vanishes only at `b = 0` or `b = -2ω`. -/
theorem tube_flat_zero_cases {ω v b w : R3} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hv1 : ‖v‖ = 1) (hw : ⟪w, ω + b⟫_ℝ = 0)
    (hw1 : ‖w‖ * ‖ω + b‖ = 1)
    (hP1 : (ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
      ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω = 0)
    (hP2 : (v - w) - ⟪ω, v - w⟫_ℝ • ω = 0) :
    b = 0 ∨ b = -(2 : ℝ) • ω := by
  have hc : ‖ω + b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  generalize hk1 : ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ = k1 at hP1
  have hq : (‖ω + b‖ ^ 2)⁻¹ • (ω + b) = (1 - k1) • ω := by
    rw [sub_smul, one_smul, ← sub_eq_zero.mp hP1]
    abel
  have hn' : ω + b = (‖ω + b‖ ^ 2 * (1 - k1)) • ω := by
    calc ω + b = (‖ω + b‖ ^ 2) • ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) := by
          rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      _ = _ := by rw [hq, smul_smul]
  generalize hk : ‖ω + b‖ ^ 2 * (1 - k1) = k at hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hn'
    exact hn hn'
  have hwω : ⟪w, ω⟫_ℝ = 0 := by
    rw [hn', inner_smul_right] at hw
    exact (mul_eq_zero.mp hw).resolve_left hk0
  have hvw : v = w := by
    have h0 : ⟪ω, v - w⟫_ℝ = 0 := by
      rw [inner_sub_right, real_inner_comm v ω, real_inner_comm w ω, hv, hwω, sub_zero]
    rw [h0, zero_smul, sub_zero] at hP2
    exact sub_eq_zero.mp hP2
  have hn1 : ‖ω + b‖ = 1 := by
    rw [← hvw, hv1, one_mul] at hw1
    exact hw1
  have hkabs : |k| = 1 := by
    have h := congrArg norm hn'
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, hn1] at h
    exact h.symm
  rcases (abs_eq zero_le_one).mp hkabs with rfl | rfl
  · left
    calc b = (ω + b) - ω := by abel
      _ = 0 := by rw [hn', one_smul, sub_self]
  · right
    calc b = (ω + b) - ω := by abel
      _ = -(2 : ℝ) • ω := by rw [hn', neg_smul, one_smul, neg_smul, two_smul]; abel

/-- T4: the exact flat tube form is the sum of the two `ω⊥`-projected squares. -/
theorem tube_flat_form_eq {ω v b w : R3} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hw : ⟪w, ω + b⟫_ℝ = 0) :
    ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 =
      ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
          ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖ ^ 2 +
        ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := tube_flat_normal_identities hω hn hv hw
  rw [← h1, ← h2, ← unit_norm_sq_sub_inner_sq hω, ← unit_norm_sq_sub_inner_sq hω]
  ring

/-- T5: the flat tube form is strictly positive away from `b = 0` and `b = -2ω`. -/
theorem tube_flat_form_pos {ω v b w : R3} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hv1 : ‖v‖ = 1) (hw : ⟪w, ω + b⟫_ℝ = 0)
    (hw1 : ‖w‖ * ‖ω + b‖ = 1) (hb0 : b ≠ 0) (hb2 : b ≠ -(2 : ℝ) • ω) :
    0 < ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 := by
  rw [tube_flat_form_eq hω hn hv hw]
  by_contra hle
  push_neg at hle
  have hA := sq_nonneg ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
    ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖
  have hB := sq_nonneg ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖
  have hA0 : ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
      ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith)
  have hB0 : ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith)
  rcases tube_flat_zero_cases hω hn hv hv1 hw hw1 (norm_eq_zero.mp hA0) (norm_eq_zero.mp hB0)
    with h | h
  · exact hb0 h
  · exact hb2 h

/-- T6: `|b| ≥ amin` on every tube level `a ≥ amin`, since the gradient has `g₂ = 1`. -/
theorem tube_b_norm_lower {g : R3} {σ t a amin : ℝ} (hg : g 2 = 1) (hσ : 0 ≤ σ)
    (ht : 1 ≤ t) (ham : 0 ≤ amin) (ha : amin ≤ a) :
    amin ≤ ‖((1 + σ) * a * t ^ σ) • g‖ := by
  have hg1 : 1 ≤ ‖g‖ := by
    have h := abs_coord_le_norm g 2
    rw [hg, abs_one] at h
    exact h
  have htσ : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ
  have ha0 : 0 ≤ a := ham.trans ha
  have h1 : a ≤ (1 + σ) * a := by nlinarith
  have h2 : (1 + σ) * a ≤ (1 + σ) * a * t ^ σ :=
    le_mul_of_one_le_right (by positivity) htσ
  have hk0 : 0 ≤ (1 + σ) * a * t ^ σ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  calc amin ≤ (1 + σ) * a * t ^ σ := by linarith
    _ ≤ (1 + σ) * a * t ^ σ * ‖g‖ := le_mul_of_one_le_right hk0 hg1

/-- T7: the smallest tube radius stays below half the target separation. -/
theorem tube_amin_radius_le {d U t σ : ℝ} (hd : 0 < d) (ht1 : 1 ≤ t) (htU : t ≤ U)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    min 1 (d / (2 * U ^ 2)) * t ^ (1 + σ) ≤ d / 2 := by
  have h1 : t ^ (1 + σ) ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  rw [Real.rpow_two] at h1
  have h2 : t ^ 2 ≤ U ^ 2 := by nlinarith
  have hU2 : 0 < U ^ 2 := by nlinarith
  have hm : min 1 (d / (2 * U ^ 2)) ≤ d / (2 * U ^ 2) := min_le_right _ _
  have hr0 : 0 ≤ t ^ (1 + σ) := Real.rpow_nonneg (by linarith) _
  calc min 1 (d / (2 * U ^ 2)) * t ^ (1 + σ) ≤ d / (2 * U ^ 2) * U ^ 2 :=
        mul_le_mul hm (h1.trans h2) hr0 (by positivity)
    _ = d / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hU2.ne']

/-- T8: the top tube level `a ≥ 2/c0 + 1` has radius larger than `t / c0`. -/
theorem tube_amax_level_seeded {c0 t σ a : ℝ} (hc0 : 0 < c0) (ht1 : 1 ≤ t) (hσ : 0 ≤ σ)
    (ha : 2 / c0 + 1 ≤ a) : t < c0 * (a * t ^ (1 + σ)) := by
  have h1 : t ≤ t ^ (1 + σ) := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : (1 : ℝ) ≤ 1 + σ)
    rwa [Real.rpow_one] at h
  have h22 : c0 * (2 / c0) = 2 := by field_simp
  have h2 : 2 + c0 ≤ c0 * a := by
    have h := mul_le_mul_of_nonneg_left ha hc0.le
    rw [mul_add, h22, mul_one] at h
    exact h
  calc t < (2 + c0) * t := by nlinarith
    _ ≤ (c0 * a) * t ^ (1 + σ) := mul_le_mul h2 h1 (by linarith) (by linarith)
    _ = c0 * (a * t ^ (1 + σ)) := by ring

/-- T9: `T0 > (1/(c0 amin))^(1/σ)` puts the top base face in the coarse seed scale. -/
theorem tube_top_face_seeded {c0 amin σ T0 : ℝ} (hc0 : 0 < c0) (ham : 0 < amin) (hσ : 0 < σ)
    (hT : (1 / (c0 * amin)) ^ (1 / σ) < T0) : 1 < c0 * amin * T0 ^ σ := by
  have hK : 0 < 1 / (c0 * amin) := by positivity
  have h1 := Real.rpow_lt_rpow (Real.rpow_nonneg hK.le _) hT hσ
  rw [← Real.rpow_mul hK.le, one_div_mul_cancel hσ.ne', Real.rpow_one] at h1
  have h2 : c0 * amin * (1 / (c0 * amin)) = 1 := by field_simp
  calc (1 : ℝ) = c0 * amin * (1 / (c0 * amin)) := h2.symm
    _ < c0 * amin * T0 ^ σ := mul_lt_mul_of_pos_left h1 (by positivity)

/-- T10: along a tube ray the lower height is `y₂ + r min(ω₂, 0)`. -/
theorem tube_min_height {y ω : R3} {r : ℝ} (hr : 0 ≤ r) :
    min ((y + r • ω) 2) (y 2) = y 2 + r * min (ω 2) 0 := by
  have h : (y + r • ω) 2 = y 2 + r * ω 2 := by simp [PiLp.add_apply, PiLp.smul_apply]
  rw [h]
  rcases le_total (ω 2) 0 with hω | hω
  · rw [min_eq_left hω, min_eq_left (by nlinarith)]
  · rw [min_eq_right hω, min_eq_right (by nlinarith), mul_zero, add_zero]

/-- T11: the coarse seed inequality is upward closed in the tube radius. -/
theorem tube_seed_upward {y ω : R3} {c0 r r' : ℝ} (hω : ‖ω‖ = 1) (hc0 : 0 < c0)
    (hr : 0 ≤ r) (hrr : r ≤ r')
    (hseed : min ((y + r • ω) 2) (y 2) < c0 * ‖(y + r • ω) - y‖) :
    min ((y + r' • ω) 2) (y 2) < c0 * ‖(y + r' • ω) - y‖ := by
  have hr' : 0 ≤ r' := hr.trans hrr
  have hn : ∀ s : ℝ, 0 ≤ s → ‖(y + s • ω) - y‖ = s := fun s hs => by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]
  rw [tube_min_height hr, hn r hr] at hseed
  rw [tube_min_height hr', hn r' hr']
  have hm : min (ω 2) 0 ≤ 0 := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.2 hrr) (by linarith : (0 : ℝ) ≤ c0 - min (ω 2) 0)]

/-- T12: a positive lower bound `m0` for the flat tube form on the fixed compact parameter set;
`m0` depends only on `amin, Bb, ε`. -/
theorem tube_flat_form_compact_min {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ ω v b w : R3, ‖ω‖ = 1 → ⟪v, ω⟫_ℝ = 0 → ‖v‖ = 1 →
      ⟪w, ω + b⟫_ℝ = 0 → ‖w‖ * ‖ω + b‖ = 1 → amin ≤ ‖b‖ → ‖b‖ ≤ Bb → ε ≤ ‖ω + b‖ →
      ε ≤ ‖b + (2 : ℝ) • ω‖ →
      m0 ≤ ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 := by
  let K : Set (R3 × R3 × R3 × R3) := {p | ‖p.1‖ = 1 ∧ ⟪p.2.1, p.1⟫_ℝ = 0 ∧ ‖p.2.1‖ = 1 ∧
    ⟪p.2.2.2, p.1 + p.2.2.1⟫_ℝ = 0 ∧ ‖p.2.2.2‖ * ‖p.1 + p.2.2.1‖ = 1 ∧ amin ≤ ‖p.2.2.1‖ ∧
    ‖p.2.2.1‖ ≤ Bb ∧ ε ≤ ‖p.1 + p.2.2.1‖ ∧ ε ≤ ‖p.2.2.1 + (2 : ℝ) • p.1‖}
  obtain ⟨c, hc, hcK⟩ : ∃ c : R3 × R3 × R3 × R3 → ℝ, Continuous c ∧
      ∀ p ∈ K, c p = (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ := by
    refine ⟨fun p => (max (‖p.1 + p.2.2.1‖ ^ 2) (ε ^ 2))⁻¹, ?_, ?_⟩
    · exact Continuous.inv₀ (by fun_prop)
        (fun p => (lt_max_of_lt_right (by positivity)).ne')
    · intro p hp
      have hle : ε ^ 2 ≤ ‖p.1 + p.2.2.1‖ ^ 2 := by nlinarith [hp.2.2.2.2.2.2.2.1]
      simp only [max_eq_left hle]
  let F : R3 × R3 × R3 × R3 → ℝ := fun p =>
    ‖p.1 - c p • (p.1 + p.2.2.1)‖ ^ 2 + ‖p.2.1 - p.2.2.2‖ ^ 2 -
      ⟪p.2.2.1, c p • (p.1 + p.2.2.1)⟫_ℝ ^ 2 - ⟪p.2.2.1, p.2.2.2⟫_ℝ ^ 2
  have hF : Continuous F := by fun_prop
  have hFK : ∀ p ∈ K, F p = ‖p.1 - (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ • (p.1 + p.2.2.1)‖ ^ 2 +
      ‖p.2.1 - p.2.2.2‖ ^ 2 - ⟪p.2.2.1, (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ • (p.1 + p.2.2.1)⟫_ℝ ^ 2 -
      ⟪p.2.2.1, p.2.2.2⟫_ℝ ^ 2 := fun p hp => by
    simp only [F, hcK p hp]
  have hKc : IsClosed K := by
    simp only [K, Set.setOf_and]
    refine (isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter
      ((isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter ((isClosed_le ?_ ?_).inter
      ((isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_))))))))
    all_goals fun_prop
  have hKb : Bornology.IsBounded K := by
    refine isBounded_iff_forall_norm_le.mpr ⟨max (max 1 Bb) (1 / ε), fun p hp => ?_⟩
    obtain ⟨h1, -, h3, -, h5, -, h7, h8, -⟩ := hp
    have hw : ‖p.2.2.2‖ ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      calc ‖p.2.2.2‖ * ε ≤ ‖p.2.2.2‖ * ‖p.1 + p.2.2.1‖ :=
            mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
        _ = 1 := h5
    refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩⟩
    · rw [h1]; exact (le_max_left _ _).trans (le_max_left _ _)
    · rw [h3]; exact (le_max_left _ _).trans (le_max_left _ _)
    · exact h7.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact hw.trans (le_max_right _ _)
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have hpos : ∀ p ∈ K, 0 < F p := fun p hp => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp
    rw [hFK p ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩]
    have hn : p.1 + p.2.2.1 ≠ 0 := fun h => by
      rw [h, norm_zero] at h8; linarith
    have hb0 : p.2.2.1 ≠ 0 := fun h => by
      rw [h, norm_zero] at h6; linarith
    have hb2 : p.2.2.1 ≠ -(2 : ℝ) • p.1 := fun h => by
      rw [h, neg_smul, neg_add_cancel, norm_zero] at h9; linarith
    exact tube_flat_form_pos h1 hn h2 h3 h4 h5 hb0 hb2
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun ω v b w h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
    have hmem : (ω, v, b, w) ∈ K := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rw [hK] at hmem
    exact hmem.elim
  · obtain ⟨p0, hp0, hmin⟩ := hKcpt.exists_isMinOn hK hF.continuousOn
    refine ⟨F p0, hpos p0 hp0, fun ω v b w h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
    have hmem : (ω, v, b, w) ∈ K := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have h : F p0 ≤ F (ω, v, b, w) := hmin hmem
    rw [hFK _ hmem] at h
    exact h

/-- T13: the horizontal gradient deviation `2 e0 |y'|` is at most `2 √(e0 T0)`. -/
theorem tube_grad_dev_le {e0 s T0 : ℝ} (he0 : 0 < e0) (hs : 0 ≤ s) (hT : e0 * s ^ 2 ≤ T0) :
    2 * e0 * s ≤ 2 * Real.sqrt (e0 * T0) := by
  have h : e0 * s ≤ Real.sqrt (e0 * T0) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- T14: scalar coefficients of `r D²r` for `r = a t^(1+σ)`. -/
theorem tube_radius_hessian_coeffs {a σ t : ℝ} (ht : 0 < t) (hσ : 0 ≤ σ) :
    a * t ^ (1 + σ) * (a * (1 + σ) * σ * t ^ (σ - 1)) = σ / (1 + σ) * (a * (1 + σ) * t ^ σ) ^ 2 ∧
      a * t ^ (1 + σ) * (a * (1 + σ) * t ^ σ) =
        a * t ^ (1 + σ) / t * (1 + σ) * (a * t ^ (1 + σ)) := by
  have h1 : t ^ (1 + σ) = t * t ^ σ := by rw [Real.rpow_add ht, Real.rpow_one]
  have h2 : t ^ (σ - 1) = t ^ σ / t := Real.rpow_sub_one ht.ne' σ
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hss : (1 + σ) * (1 + σ)⁻¹ = 1 := mul_inv_cancel₀ (by linarith : (0 : ℝ) < 1 + σ).ne'
  rw [h1, h2]
  constructor
  · linear_combination (a ^ 2 * (1 + σ) * σ * (t ^ σ) ^ 2) * htt -
      (a ^ 2 * σ * (1 + σ) * (t ^ σ) ^ 2) * hss
  · linear_combination (-(a ^ 2 * (1 + σ) * t * (t ^ σ) ^ 2)) * htt

/-- T15: height bound in an excluded configuration `‖b + j ω‖ ≤ ε`, `b = (1+σ)(r/t) g`. -/
theorem tube_excluded_height {ω g : R3} {j ε r t σ y2 : ℝ} (hj : 0 < j) (hg : g 2 = 1)
    (hr : 0 < r) (ht : 0 < t) (hσ : 0 ≤ σ) (hy : y2 < t)
    (hb : ‖((1 + σ) * (r / t)) • g + j • ω‖ ≤ ε) :
    y2 + r * ω 2 < r * ((1 + σ) / ((1 + σ) * (r / t)) + (ε - (1 + σ) * (r / t)) / j) := by
  have h1σ : (1 + σ) ≠ 0 := (by linarith : (0 : ℝ) < 1 + σ).ne'
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hrt : r * ((1 + σ) / ((1 + σ) * (r / t))) = t := by
    rw [div_mul_eq_div_div, div_self h1σ, one_div_div]
    linear_combination t * hrr
  set κ := (1 + σ) * (r / t) with hκ
  have hcoord : |(κ • g + j • ω) 2| ≤ ε := (abs_coord_le_norm _ 2).trans hb
  have h2 : (κ • g + j • ω) 2 = κ + j * ω 2 := by
    simp [PiLp.add_apply, PiLp.smul_apply, hg]
  rw [h2] at hcoord
  have hω2 : ω 2 ≤ (ε - κ) / j := by
    rw [le_div_iff₀ hj]
    linarith [(abs_le.mp hcoord).2]
  have h3 := mul_le_mul_of_nonneg_left hω2 hr.le
  rw [mul_add, hrt]
  linarith

/-- T16: the `j = 1` excluded configuration lies below the seed threshold `c0`. -/
theorem tube_excluded_scalar_one {c0 η σ ε κ : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hc0 : 13 * η ≤ c0) (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hκ : 0 < κ)
    (hκη : 1 - η ≤ κ * (1 + η)) :
    (1 + σ) / κ + (ε - κ) < c0 := by
  have h1 : 1 - 2 * η ≤ κ := by nlinarith
  have h2 : 1 - 4 * η ≤ κ ^ 2 := by nlinarith
  have h3 : 6 * η ≤ (c0 - ε) * κ := by nlinarith
  have h4 : (1 + σ) / κ < c0 - ε + κ := by
    rw [div_lt_iff₀ hκ]
    nlinarith
  linarith

/-- T17: `‖κ g + j ω‖ ≤ ε` and `‖g - e₂‖ ≤ η` force `κ (1 + η) ≥ j - η`. -/
theorem tube_excluded_kappa_link {ω g : R3} {j κ ε η : ℝ} (hω : ‖ω‖ = 1) (hj : 0 < j)
    (hκ : 0 ≤ κ) (hg : ‖g - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ η) (hε : ε ≤ η)
    (hb : ‖κ • g + j • ω‖ ≤ ε) : j - η ≤ κ * (1 + η) := by
  have he : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hg1 : ‖g‖ ≤ 1 + η := by
    have h := norm_add_le (g - EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    rw [sub_add_cancel, he] at h
    linarith
  have hjω : ‖j • ω‖ = j := by rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hj]
  have hb' : j - ε ≤ ‖κ • g‖ := by
    have h := norm_sub_le (κ • g + j • ω) (κ • g)
    rw [add_sub_cancel_left, hjω] at h
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ] at hb'
  nlinarith [mul_le_mul_of_nonneg_left hg1 hκ]

/-- T18: the `j = 2` excluded configuration lies below the seed threshold `c0`. -/
theorem tube_excluded_scalar_two {c0 η σ ε κ : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    (hc0 : 0 < c0) (hσ : σ ≤ η) (hε : ε ≤ η) (hκ : 0 < κ)
    (hκη : 2 - η ≤ κ * (1 + η)) :
    (1 + σ) / κ + (ε - κ) / 2 < c0 := by
  have h1 : 2 - 3 * η ≤ κ := by nlinarith
  have h2 : 11 / 10 < κ * (κ - ε) / 2 := by nlinarith
  have h4 : (1 + σ) / κ < c0 + (κ - ε) / 2 := by
    rw [div_lt_iff₀ hκ]
    nlinarith
  linarith

/-- T19: near `b = -ω` the outer point is below the coarse seed height `c0 r`. -/
theorem tube_excluded_one_low {ω g : R3} {c0 η σ ε r t y2 : ℝ} (hω : ‖ω‖ = 1) (hg : g 2 = 1)
    (hge : ‖g - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ η) (hr : 0 < r) (ht : 0 < t)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hc0 : 13 * η ≤ c0)
    (hy : y2 < t) (hb : ‖((1 + σ) * (r / t)) • g + ω‖ ≤ ε) :
    y2 + r * ω 2 < c0 * r := by
  have hb1 : ‖((1 + σ) * (r / t)) • g + (1 : ℝ) • ω‖ ≤ ε := by rwa [one_smul]
  have hκ : 0 < (1 + σ) * (r / t) := by positivity
  have h1 := tube_excluded_height one_pos hg hr ht hσ0 hy hb1
  have h2 := tube_excluded_kappa_link hω one_pos hκ.le hge hε hb1
  have h3 := tube_excluded_scalar_one hη hη4 hc0 hσ0 hσ hε hκ h2
  rw [div_one] at h1
  nlinarith

/-- T20: near `b = -2ω` the outer point is below the coarse seed height `c0 r`. -/
theorem tube_excluded_two_low {ω g : R3} {c0 η σ ε r t y2 : ℝ} (hω : ‖ω‖ = 1) (hg : g 2 = 1)
    (hge : ‖g - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ η) (hr : 0 < r) (ht : 0 < t)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc0 : 0 < c0)
    (hy : y2 < t) (hb : ‖((1 + σ) * (r / t)) • g + (2 : ℝ) • ω‖ ≤ ε) :
    y2 + r * ω 2 < c0 * r := by
  have hκ : 0 < (1 + σ) * (r / t) := by positivity
  have h1 := tube_excluded_height two_pos hg hr ht hσ0 hy hb
  have h2 := tube_excluded_kappa_link hω two_pos hκ.le hge hε hb
  have h3 := tube_excluded_scalar_two hη hη10 hc0 hσ hε hκ h2
  nlinarith

/-- T21: every target separation `D ≥ d` sits at a tube level strictly above `amin`. -/
theorem tube_target_level_gt {d D U t σ : ℝ} (hd : 0 < d) (hdD : d ≤ D) (ht1 : 1 ≤ t)
    (htU : t ≤ U) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    min 1 (d / (2 * U ^ 2)) < D / t ^ (1 + σ) := by
  have hpos : 0 < t ^ (1 + σ) := Real.rpow_pos_of_pos (by linarith) _
  rw [lt_div_iff₀ hpos]
  have h := tube_amin_radius_le hd ht1 htU hσ0 hσ1
  linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v054: actual tube functions and their first Frechet jets (J1-J3 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- The actual tube height `t(Y) = M + Y₂ + e0 (Y₀² + Y₁²)`. -/
def tubeHeight (M e0 : ℝ) (Y : R3) : ℝ := M + Y 2 + e0 * (Y 0 ^ 2 + Y 1 ^ 2)

/-- The actual tube radius `r_a(Y) = a t(Y)^(1+σ)`. -/
def tubeRadius (M e0 a σ : ℝ) (Y : R3) : ℝ := a * tubeHeight M e0 Y ^ (1 + σ)

/-- The actual pair phase `ρ(X,Y) = (‖X-Y‖² - r_a(Y)²)/2`. -/
def tubePhase (M e0 a σ : ℝ) (z : R3 × R3) : ℝ :=
  (‖z.1 - z.2‖ ^ 2 - tubeRadius M e0 a σ z.2 ^ 2) / 2

/-- The actual differential `dt_Y = (2 e0 Y₀, 2 e0 Y₁, 1)`. -/
def tubeHeightDeriv (e0 : ℝ) (Y : R3) : R3 →L[ℝ] ℝ :=
  (2 * e0 * Y 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) +
    (2 * e0 * Y 1) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) +
    EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)

theorem tubeHeightDeriv_apply (e0 : ℝ) (Y U : R3) :
    tubeHeightDeriv e0 Y U = 2 * e0 * Y 0 * U 0 + 2 * e0 * Y 1 * U 1 + U 2 := by
  simp [tubeHeightDeriv] <;> ring

/-- J1: the true Frechet derivative of the actual tube height. -/
theorem tube_height_hasFDerivAt (M e0 : ℝ) (Y : R3) :
    HasFDerivAt (tubeHeight M e0) (tubeHeightDeriv e0 Y) Y := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := Y)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := Y)
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := Y)
  have h := (h2.const_add M).add (((h0.pow 2).add (h1.pow 2)).const_mul e0)
  have hf : tubeHeight M e0 = fun x : R3 => M + EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) x +
      e0 * (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) x ^ 2 +
        EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) x ^ 2) := by
    funext x
    simp [tubeHeight]
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun U => ?_)
  rw [tubeHeightDeriv_apply]
  simp <;> ring

/-- J2: on `t > 0`, `Dr = a (1+σ) t^σ dt`. -/
theorem tube_radius_hasFDerivAt (M e0 a σ : ℝ) {Y : R3} (ht : 0 < tubeHeight M e0 Y) :
    HasFDerivAt (tubeRadius M e0 a σ)
      ((a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightDeriv e0 Y) Y := by
  have h := ((tube_height_hasFDerivAt M e0 Y).rpow_const (p := 1 + σ)
    (Or.inl ht.ne')).const_mul a
  have hs : (1 + σ - 1) = σ := by ring
  rw [hs, smul_smul] at h
  have hc : a * ((1 + σ) * tubeHeight M e0 Y ^ σ) = a * (1 + σ) * tubeHeight M e0 Y ^ σ := by
    ring
  rw [hc] at h
  exact h

/-- J3: on `t(Y) > 0`, `Dρ(X,Y)(W₁,W₂) = ⟪X-Y, W₁-W₂⟫ - r Dr(W₂)`. -/
theorem tube_phase_fderiv_apply (M e0 a σ : ℝ) {X Y : R3} (ht : 0 < tubeHeight M e0 Y) :
    DifferentiableAt ℝ (tubePhase M e0 a σ) (X, Y) ∧ ∀ W : R3 × R3,
      fderiv ℝ (tubePhase M e0 a σ) (X, Y) W = ⟪X - Y, W.1 - W.2⟫_ℝ -
        tubeRadius M e0 a σ Y *
          (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y W.2) := by
  have hd : HasFDerivAt (fun z : R3 × R3 => z.1 - z.2)
      (ContinuousLinearMap.fst ℝ R3 R3 - ContinuousLinearMap.snd ℝ R3 R3) (X, Y) :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hn := hd.norm_sq
  have hs : HasFDerivAt (Prod.snd : R3 × R3 → R3) (ContinuousLinearMap.snd ℝ R3 R3) (X, Y) :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius M e0 a σ)
      ((a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightDeriv e0 Y) (Prod.snd (X, Y)) :=
    tube_radius_hasFDerivAt M e0 a σ ht
  have hr : HasFDerivAt (fun z : R3 × R3 => tubeRadius M e0 a σ z.2)
      (((a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightDeriv e0 Y).comp
        (ContinuousLinearMap.snd ℝ R3 R3)) (X, Y) :=
    hr0.comp (X, Y) hs
  have h := (hn.sub (hr.pow 2)).const_mul (1 / 2 : ℝ)
  have hf : tubePhase M e0 a σ = fun z : R3 × R3 =>
      (1 / 2 : ℝ) * (‖z.1 - z.2‖ ^ 2 - tubeRadius M e0 a σ z.2 ^ 2) := by
    funext z
    simp only [tubePhase]
    ring
  rw [hf]
  refine ⟨h.differentiableAt, fun W => ?_⟩
  have hD : fderiv ℝ (fun z : R3 × R3 =>
      (1 / 2 : ℝ) * (‖z.1 - z.2‖ ^ 2 - tubeRadius M e0 a σ z.2 ^ 2)) (X, Y) = _ := h.fderiv
  rw [hD]
  simp [inner_sub_left, inner_sub_right]
  ring

/-- J4: the true derivative of `Y ↦ dt_Y` is `D²t(V)(U) = 2 e0 (V₀U₀ + V₁U₁)`. -/
theorem tube_height_deriv_hasFDerivAt (e0 : ℝ) (Y : R3) :
    ∃ D : R3 →L[ℝ] R3 →L[ℝ] ℝ, HasFDerivAt (tubeHeightDeriv e0) D Y ∧
      ∀ V U : R3, D V U = 2 * e0 * (V 0 * U 0 + V 1 * U 1) := by
  have h0 := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt (x := Y)).const_mul
    (2 * e0)).smul_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3))
  have h1 := (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).hasFDerivAt (x := Y)).const_mul
    (2 * e0)).smul_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))
  have h := (h0.add h1).add (hasFDerivAt_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) Y)
  have hf : tubeHeightDeriv e0 = fun Y' : R3 =>
      (2 * e0 * EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) Y') •
          EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3) +
        (2 * e0 * EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) Y') •
          EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3) +
        EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) := by
    funext Y'
    rfl
  rw [hf]
  refine ⟨_, h, fun V U => ?_⟩
  simp
  ring

/-- J5: on `t > 0`, the true derivative of `Y ↦ Dr_Y = a(1+σ) t^σ dt_Y` is
`D²r(V)(U) = a(1+σ) σ t^(σ-1) dt(V) dt(U) + a(1+σ) t^σ D²t(V)(U)`. -/
theorem tube_radius_deriv_hasFDerivAt (M e0 a σ : ℝ) {Y : R3} (ht : 0 < tubeHeight M e0 Y) :
    ∃ D : R3 →L[ℝ] R3 →L[ℝ] ℝ,
      HasFDerivAt (fun Y' : R3 => (a * (1 + σ) * tubeHeight M e0 Y' ^ σ) • tubeHeightDeriv e0 Y')
        D Y ∧
      ∀ V U : R3, D V U = a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) *
          tubeHeightDeriv e0 Y V * tubeHeightDeriv e0 Y U +
        a * (1 + σ) * tubeHeight M e0 Y ^ σ * (2 * e0 * (V 0 * U 0 + V 1 * U 1)) := by
  obtain ⟨D2, hD2, hD2e⟩ := tube_height_deriv_hasFDerivAt e0 Y
  have hk := ((tube_height_hasFDerivAt M e0 Y).rpow_const (p := σ) (Or.inl ht.ne')).const_mul
    (a * (1 + σ))
  refine ⟨_, hk.smul hD2, fun V U => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hD2e]
  ring

open scoped Topology in
/-- J6(a,b): on a neighborhood of `(X,Y)` with `t(Y) > 0`, the pair phase has the explicit first jet
`G z = ⟪z₁-z₂, ·₁-·₂⟫ - r(z₂) k(z₂) dt_{z₂}(·₂)`, `k = a(1+σ) t^σ`. -/
theorem tube_phase_hasFDerivAt_eventually (M e0 a σ : ℝ) {X Y : R3}
    (ht : 0 < tubeHeight M e0 Y) :
    ∀ᶠ z in 𝓝 (X, Y), HasFDerivAt (tubePhase M e0 a σ)
      ((innerSL ℝ (z.1 - z.2)).comp
          (ContinuousLinearMap.fst ℝ R3 R3 - ContinuousLinearMap.snd ℝ R3 R3) -
        (tubeRadius M e0 a σ z.2 * (a * (1 + σ) * tubeHeight M e0 z.2 ^ σ)) •
          (tubeHeightDeriv e0 z.2).comp (ContinuousLinearMap.snd ℝ R3 R3)) z := by
  have hcont : ContinuousAt (fun z : R3 × R3 => tubeHeight M e0 z.2) (X, Y) :=
    ContinuousAt.comp (f := Prod.snd) (x := (X, Y))
      (tube_height_hasFDerivAt M e0 Y).continuousAt continuousAt_snd
  have hev : ∀ᶠ z in 𝓝 (X, Y), 0 < tubeHeight M e0 z.2 := hcont.eventually (lt_mem_nhds ht)
  refine hev.mono fun z hz => ?_
  have hd : HasFDerivAt (fun w : R3 × R3 => w.1 - w.2)
      (ContinuousLinearMap.fst ℝ R3 R3 - ContinuousLinearMap.snd ℝ R3 R3) z :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hn := hd.norm_sq
  have hs : HasFDerivAt (Prod.snd : R3 × R3 → R3) (ContinuousLinearMap.snd ℝ R3 R3) z :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius M e0 a σ)
      ((a * (1 + σ) * tubeHeight M e0 z.2 ^ σ) • tubeHeightDeriv e0 z.2) (Prod.snd z) :=
    tube_radius_hasFDerivAt M e0 a σ hz
  have hr : HasFDerivAt (fun w : R3 × R3 => tubeRadius M e0 a σ w.2)
      (((a * (1 + σ) * tubeHeight M e0 z.2 ^ σ) • tubeHeightDeriv e0 z.2).comp
        (ContinuousLinearMap.snd ℝ R3 R3)) z :=
    hr0.comp z hs
  have h := (hn.sub (hr.pow 2)).const_mul (1 / 2 : ℝ)
  have hf : tubePhase M e0 a σ = fun w : R3 × R3 =>
      (1 / 2 : ℝ) * (‖w.1 - w.2‖ ^ 2 - tubeRadius M e0 a σ w.2 ^ 2) := by
    funext w
    simp only [tubePhase]
    ring
  rw [hf]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  simp [inner_sub_left, inner_sub_right]
  ring

open scoped Topology in
/-- J6(c,d): the true second jet of the actual pair phase on `t(Y) > 0`:
`D²ρ(W,V) = ⟪W₁-W₂,V₁-V₂⟫ - Dr(W₂)Dr(V₂) - r D²r(W₂,V₂)`. -/
theorem tube_phase_second_jet (M e0 a σ : ℝ) {X Y : R3} (ht : 0 < tubeHeight M e0 Y) :
    ∃ D : R3 × R3 →L[ℝ] R3 × R3 →L[ℝ] ℝ,
      HasFDerivAt (fderiv ℝ (tubePhase M e0 a σ)) D (X, Y) ∧ ∀ W V : R3 × R3,
        D W V = ⟪W.1 - W.2, V.1 - V.2⟫_ℝ -
          (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y W.2) *
            (a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y V.2) -
          tubeRadius M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) *
              tubeHeightDeriv e0 Y W.2 * tubeHeightDeriv e0 Y V.2 +
            a * (1 + σ) * tubeHeight M e0 Y ^ σ *
              (2 * e0 * (W.2 0 * V.2 0 + W.2 1 * V.2 1))) := by
  have hEv := (tube_phase_hasFDerivAt_eventually M e0 a σ (X := X) ht).mono
    fun z hz => hz.fderiv
  have hd : HasFDerivAt (fun z : R3 × R3 => z.1 - z.2)
      (ContinuousLinearMap.fst ℝ R3 R3 - ContinuousLinearMap.snd ℝ R3 R3) (X, Y) :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  have hI0 : HasFDerivAt (fun v : R3 => (innerSL ℝ v : R3 →L[ℝ] ℝ))
      (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ) ((fun z : R3 × R3 => z.1 - z.2) (X, Y)) :=
    (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ).hasFDerivAt
  have hI := hI0.comp (X, Y) hd
  have hA := hI.clm_comp (hasFDerivAt_const
    (ContinuousLinearMap.fst ℝ R3 R3 - ContinuousLinearMap.snd ℝ R3 R3) (X, Y))
  have hs : HasFDerivAt (Prod.snd : R3 × R3 → R3) (ContinuousLinearMap.snd ℝ R3 R3) (X, Y) :=
    hasFDerivAt_snd
  have hr0 : HasFDerivAt (tubeRadius M e0 a σ)
      ((a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightDeriv e0 Y) (Prod.snd (X, Y)) :=
    tube_radius_hasFDerivAt M e0 a σ ht
  have hk0 : HasFDerivAt (fun Y' : R3 => a * (1 + σ) * tubeHeight M e0 Y' ^ σ)
      ((a * (1 + σ)) • ((σ * tubeHeight M e0 Y ^ (σ - 1)) • tubeHeightDeriv e0 Y))
      (Prod.snd (X, Y)) :=
    ((tube_height_hasFDerivAt M e0 Y).rpow_const (p := σ) (Or.inl ht.ne')).const_mul
      (a * (1 + σ))
  obtain ⟨D2, hD2, hD2e⟩ := tube_height_deriv_hasFDerivAt e0 Y
  have hD20 : HasFDerivAt (tubeHeightDeriv e0) D2 (Prod.snd (X, Y)) := hD2
  have hc := (hr0.comp (X, Y) hs).mul (hk0.comp (X, Y) hs)
  have hT := (hD20.comp (X, Y) hs).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.snd ℝ R3 R3) (X, Y))
  have hG := hA.sub (hc.smul hT)
  have hi : ∀ u w : R3, (innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ) u w = ⟪u, w⟫_ℝ := fun u w => rfl
  refine ⟨_, hG.congr_of_eventuallyEq hEv, fun W V => ?_⟩
  simp [hD2e, hi, inner_sub_left, inner_sub_right] <;> ring

/-- The gradient vector `g_Y = (2 e0 Y₀, 2 e0 Y₁, 1)` of the actual tube height. -/
def tubeHeightGrad (e0 : ℝ) (Y : R3) : R3 := WithLp.toLp 2 ![2 * e0 * Y 0, 2 * e0 * Y 1, 1]

theorem tubeHeightDeriv_eq_inner (e0 : ℝ) (Y U : R3) :
    tubeHeightDeriv e0 Y U = ⟪tubeHeightGrad e0 Y, U⟫_ℝ := by
  rw [tubeHeightDeriv_apply]
  simp [tubeHeightGrad, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-- J7: at `X = Y + r ω` the two partial first jets are `r⟪ω,·⟫` and `-r⟪ω + b,·⟫`, `b = k g_Y`. -/
theorem tube_phase_partial_jets (M e0 a σ : ℝ) {Y ω : R3} (ht : 0 < tubeHeight M e0 Y)
    (W1 W2 : R3) :
    fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (W1, 0) =
        tubeRadius M e0 a σ Y * ⟪ω, W1⟫_ℝ ∧
      fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (0, W2) =
        -(tubeRadius M e0 a σ Y *
          ⟪ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y, W2⟫_ℝ) := by
  obtain ⟨-, hJ⟩ := tube_phase_fderiv_apply M e0 a σ (X := Y + tubeRadius M e0 a σ Y • ω) ht
  refine ⟨?_, ?_⟩
  · rw [hJ]
    simp [inner_smul_left]
  · rw [hJ, tubeHeightDeriv_eq_inner]
    simp [inner_smul_left, inner_add_left, inner_neg_right]
    ring

/-- E1: the identity metric has zero native coordinate connection. -/
theorem euclidean_connection_zero (Q : R3 → R3 →L[ℝ] R3) (x X Y : R3) :
    ConnectionError.coordinateConnectionField Q
      (MetricOperator.metricOperatorField (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)))
      x X Y = 0 := by
  have h : fderiv ℝ (MetricOperator.metricOperatorField
      (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))) x = 0 := by
    show fderiv ℝ (fun _ : R3 => MetricOperator.matrixOperatorMap
      (1 : Matrix (Fin 3) (Fin 3) ℝ)) x = 0
    exact fderiv_const_apply _
  rw [ConnectionError.coordinateConnectionField_apply, h,
    ← ConnectionError.coordinateConnectionLinearMap_eq,
    ConnectionError.coordinateConnectionLinearMap_apply]
  simp

/-- E2: the identity matrix acts as the identity operator. -/
theorem euclidean_matrixOperator_one (X : R3) :
    MetricOperator.matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ) X = X := by
  ext i
  show ∑ j : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * X j = X i
  simp [Matrix.one_apply]

/-- E2: the identity metric has identity metric operator and identity inverse action. -/
theorem euclidean_metricOperator_one (x X : R3) :
    MetricOperator.metricOperatorField (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) x X = X ∧
      MetricOperator.matrixOperatorMap ((1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) X = X := by
  refine ⟨euclidean_matrixOperator_one X, ?_⟩
  rw [inv_one]
  exact euclidean_matrixOperator_one X

/-- E3: the native coordinate vector of a Euclidean covector `⟪v,·⟫` is `v`. -/
theorem euclidean_coordinate_riesz (ell : R3 →L[ℝ] ℝ) (v : R3) (h : ∀ U : R3, ell U = ⟪v, U⟫_ℝ) :
    WithLp.toLp 2 (fun i : Fin 3 => ell (MetricVolume.coordinateVector i)) = v := by
  ext i
  simp [h, MetricVolume.coordinateVector, EuclideanSpace.inner_single_right]

/-- H1: the Hessian sum at `(P,-Q)` and `(V₁,V₂)` for the J6 second-jet formula. -/
theorem tube_phase_hessian_sum {D : R3 × R3 →L[ℝ] R3 × R3 →L[ℝ] ℝ} {d : R3 →L[ℝ] ℝ}
    {k s rr e0 : ℝ}
    (hD : ∀ W V : R3 × R3, D W V = ⟪W.1 - W.2, V.1 - V.2⟫_ℝ - (k * d W.2) * (k * d V.2) -
      rr * (s * d W.2 * d V.2 + k * (2 * e0 * (W.2 0 * V.2 0 + W.2 1 * V.2 1))))
    (P Q V1 V2 : R3) :
    D (P, -Q) (P, -Q) + D (V1, V2) (V1, V2) =
      ⟪P + Q, P + Q⟫_ℝ + ⟪V1 - V2, V1 - V2⟫_ℝ - (k * d Q) ^ 2 - (k * d V2) ^ 2 -
        rr * (s * d Q ^ 2 + k * (2 * e0 * (Q 0 ^ 2 + Q 1 ^ 2)) +
          s * d V2 ^ 2 + k * (2 * e0 * (V2 0 ^ 2 + V2 1 ^ 2))) := by
  rw [hD, hD]
  simp only [map_neg, sub_neg_eq_add, PiLp.neg_apply]
  ring

/-- H2: the horizontal square is at most `2 ‖Q‖²`. -/
theorem tube_horizontal_sq_le (Q : R3) : Q 0 ^ 2 + Q 1 ^ 2 ≤ 2 * ‖Q‖ ^ 2 := by
  have h0 := abs_coord_le_norm Q 0
  have h1 := abs_coord_le_norm Q 1
  have e0 : Q 0 ^ 2 ≤ ‖Q‖ ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Q 0)]
  have e1 : Q 1 ^ 2 ≤ ‖Q‖ ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Q 1)]
  linarith

/-- H3: `|dt_Y(U)| ≤ ‖g_Y‖ ‖U‖`. -/
theorem tube_height_deriv_abs_le (e0 : ℝ) (Y U : R3) :
    |tubeHeightDeriv e0 Y U| ≤ ‖tubeHeightGrad e0 Y‖ * ‖U‖ := by
  rw [tubeHeightDeriv_eq_inner]
  exact abs_real_inner_le_norm _ _

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v056: native normalization and imaginary-vector constraints (N1-N4 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- N1: the native normalization of `b1 = r ω` is `a1 = r⁻¹ ω`. -/
theorem tube_native_a1 {ω : R3} {r : ℝ} (hr : r ≠ 0) (hω : ‖ω‖ = 1) :
    (⟪r • ω, r • ω⟫_ℝ)⁻¹ • (r • ω) = r⁻¹ • ω := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hω, smul_smul]
  congr 1
  first | (field_simp; done) | (field_simp; ring)

/-- N2: the native normalization of `b2 = -(r q)` is `a2 = -((r ‖q‖²)⁻¹) q`. -/
theorem tube_native_a2 {q : R3} {r : ℝ} (hr : r ≠ 0) (hq : q ≠ 0) :
    (⟪-(r • q), -(r • q)⟫_ℝ)⁻¹ • (-(r • q)) = -((r * ‖q‖ ^ 2)⁻¹) • q := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  rw [inner_neg_left, inner_neg_right, neg_neg, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, smul_neg, smul_smul, neg_smul]
  congr 2
  first | (field_simp; done) | (field_simp; ring)

/-- N3: the literal identity-metric constraints on `v1` give `‖r v1‖ = 1` and `r v1 ⊥ ω`. -/
theorem tube_native_v1_constraints {ω v : R3} {r : ℝ} (hr : r ≠ 0) (hω : ‖ω‖ = 1)
    (h1 : ⟪v, r⁻¹ • ω⟫_ℝ = 0) (h2 : ⟪v, v⟫_ℝ = ⟪r⁻¹ • ω, r⁻¹ • ω⟫_ℝ) :
    ‖r • v‖ = 1 ∧ ⟪r • v, ω⟫_ℝ = 0 := by
  rw [real_inner_smul_right] at h1
  have h1' : ⟪v, ω⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (inv_ne_zero hr)
    · exact h
  refine ⟨?_, by rw [real_inner_smul_left, h1', mul_zero]⟩
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, hω, mul_one,
    norm_inv] at h2
  have hr' : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hsq : ‖r • v‖ ^ 2 = 1 := by
    rw [norm_smul, mul_pow, h2]
    first | (field_simp; done) | (field_simp; ring)
  have hnn : 0 ≤ ‖r • v‖ := norm_nonneg _
  nlinarith [hsq, hnn]

/-- N4: the literal identity-metric constraints on `v2` give `r v2 ⊥ q` and `‖r v2‖ ‖q‖ = 1`. -/
theorem tube_native_v2_constraints {q v : R3} {r : ℝ} (hr : r ≠ 0) (hq : q ≠ 0)
    (h1 : ⟪v, -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ = 0)
    (h2 : ⟪v, v⟫_ℝ = ⟪-((r * ‖q‖ ^ 2)⁻¹) • q, -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ) :
    ⟪r • v, q⟫_ℝ = 0 ∧ ‖r • v‖ * ‖q‖ = 1 := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hc : -((r * ‖q‖ ^ 2)⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero hr (pow_ne_zero 2 hn)))
  rw [real_inner_smul_right] at h1
  have h1' : ⟪v, q⟫_ℝ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · exact h
  refine ⟨by rw [real_inner_smul_left, h1', mul_zero], ?_⟩
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, mul_pow, norm_neg,
    norm_inv, norm_mul, norm_pow, norm_norm] at h2
  have hr' : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hsq : (‖r • v‖ * ‖q‖) ^ 2 = 1 := by
    rw [norm_smul, mul_pow, mul_pow, h2]
    first | (field_simp; done) | (field_simp; ring)
  have hnn : 0 ≤ ‖r • v‖ * ‖q‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hsq, hnn]

/-- N5: at `X = Y + r ω` both native partial covectors `ell1 = ell ∘ inl`, `ell2 = ell ∘ inr` are
nonzero: `ell1 ω = r` and `ell2 q = -r ‖q‖²`, `q = ω + b`. -/
theorem tube_native_ell_ne_zero (M e0 a σ : ℝ) {Y ω : R3} (ht : 0 < tubeHeight M e0 Y)
    (hr : tubeRadius M e0 a σ Y ≠ 0) (hω : ‖ω‖ = 1)
    (hq : ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y ≠ 0) :
    (fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y)).comp
        (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      (fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y)).comp
        (ContinuousLinearMap.inr ℝ R3 R3) ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := (tube_phase_partial_jets M e0 a σ (ω := ω) ht ω 0).1
    have h0 := congrArg (fun L : R3 →L[ℝ] ℝ => L ω) h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.zero_apply] at h0
    rw [h1, real_inner_self_eq_norm_sq, hω, one_pow, mul_one] at h0
    exact hr h0
  · have h2 := (tube_phase_partial_jets M e0 a σ (ω := ω) ht 0
      (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)).2
    have h0 := congrArg (fun L : R3 →L[ℝ] ℝ =>
      L (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)) h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply] at h0
    rw [h2, real_inner_self_eq_norm_sq] at h0
    have hpos : 0 < ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr hq) 2
    rcases mul_eq_zero.mp (neg_eq_zero.mp h0) with h' | h'
    · exact hr h'
    · exact absurd h' (ne_of_gt hpos)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v057: native identity-metric ProductHessianStrictAt assembly (N6 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- N6: the literal native `ProductHessianStrictAt` at the identity metrics for the SAME `tubePhase`
at `(Y + r ω, Y)` reduces to the exact H1/J6 scalar at `P = a1 = r⁻¹ ω`, `Q = a2 = -((r‖q‖²)⁻¹) q`,
for all `(v1, v2)` obeying the derived constraints. -/
theorem tube_native_strict_of_form (M e0 a σ : ℝ) {Y ω q : R3} {r k s : ℝ}
    (ht : 0 < tubeHeight M e0 Y) (hω : ‖ω‖ = 1)
    (hrd : tubeRadius M e0 a σ Y = r) (hkd : a * (1 + σ) * tubeHeight M e0 Y ^ σ = k)
    (hsd : a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) = s)
    (hqd : ω + k • tubeHeightGrad e0 Y = q) (hr : r ≠ 0) (hq : q ≠ 0)
    (hE : ∀ v1 v2 : R3, ‖r • v1‖ = 1 → ⟪r • v1, ω⟫_ℝ = 0 → ⟪r • v2, q⟫_ℝ = 0 →
      ‖r • v2‖ * ‖q‖ = 1 →
      0 < ⟪r⁻¹ • ω + -((r * ‖q‖ ^ 2)⁻¹) • q, r⁻¹ • ω + -((r * ‖q‖ ^ 2)⁻¹) • q⟫_ℝ +
        ⟪v1 - v2, v1 - v2⟫_ℝ - (k * tubeHeightDeriv e0 Y (-((r * ‖q‖ ^ 2)⁻¹) • q)) ^ 2 -
        (k * tubeHeightDeriv e0 Y v2) ^ 2 -
        r * (s * tubeHeightDeriv e0 Y (-((r * ‖q‖ ^ 2)⁻¹) • q) ^ 2 +
          k * (2 * e0 * ((-((r * ‖q‖ ^ 2)⁻¹) • q) 0 ^ 2 + (-((r * ‖q‖ ^ 2)⁻¹) • q) 1 ^ 2)) +
          s * tubeHeightDeriv e0 Y v2 ^ 2 + k * (2 * e0 * (v2 0 ^ 2 + v2 1 ^ 2)))) :
    ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + r • ω) Y (tubePhase M e0 a σ) := by
  subst hrd hkd hsd hqd
  obtain ⟨D, hD, hDe⟩ := tube_phase_second_jet M e0 a σ
    (X := Y + tubeRadius M e0 a σ Y • ω) ht
  have hDf := hD.fderiv
  have hJ1' : ∀ U : R3, fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (U, 0) =
      tubeRadius M e0 a σ Y * ⟪ω, U⟫_ℝ := fun U => (tube_phase_partial_jets M e0 a σ ht U 0).1
  have hJ2' : ∀ U : R3, fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (0, U) =
      -(tubeRadius M e0 a σ Y *
        ⟪ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y, U⟫_ℝ) :=
    fun U => (tube_phase_partial_jets M e0 a σ ht 0 U).2
  obtain ⟨hl1, hl2⟩ := tube_native_ell_ne_zero M e0 a σ ht hr hω hq
  unfold ProductHessianStrictAt
  intro ell ell1 ell2 M1 M2 Gamma1 Gamma2 b1 b2 a1 a2 H
  have hM1 : ∀ X : R3, M1 X = X := fun X => euclidean_matrixOperator_one X
  have hM2 : ∀ X : R3, M2 X = X := fun X => euclidean_matrixOperator_one X
  have hG1 : ∀ X Z : R3, Gamma1 X Z = 0 := fun X Z => euclidean_connection_zero _ _ _ _
  have hG2 : ∀ X Z : R3, Gamma2 X Z = 0 := fun X Z => euclidean_connection_zero _ _ _ _
  have hb1 : b1 = tubeRadius M e0 a σ Y • ω := by
    show MetricOperator.matrixOperatorMap ((1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹)
      (WithLp.toLp 2 (fun i : Fin 3 => ell1 (MetricVolume.coordinateVector i))) = _
    rw [(euclidean_metricOperator_one Y _).2]
    refine euclidean_coordinate_riesz ell1 _ (fun U => ?_)
    show fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (U, 0) = _
    rw [hJ1', real_inner_smul_left]
  have hb2 : b2 = -(tubeRadius M e0 a σ Y •
      (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)) := by
    show MetricOperator.matrixOperatorMap ((1 : Matrix (Fin 3) (Fin 3) ℝ)⁻¹)
      (WithLp.toLp 2 (fun i : Fin 3 => ell2 (MetricVolume.coordinateVector i))) = _
    rw [(euclidean_metricOperator_one Y _).2]
    refine euclidean_coordinate_riesz ell2 _ (fun U => ?_)
    show fderiv ℝ (tubePhase M e0 a σ) (Y + tubeRadius M e0 a σ Y • ω, Y) (0, U) = _
    rw [hJ2', inner_neg_left, real_inner_smul_left]
  have ha1 : a1 = (tubeRadius M e0 a σ Y)⁻¹ • ω := by
    show (⟪M1 b1, b1⟫_ℝ)⁻¹ • b1 = _
    rw [hM1, hb1]
    exact tube_native_a1 hr hω
  have ha2 : a2 = -((tubeRadius M e0 a σ Y *
      ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹) •
      (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y) := by
    show (⟪M2 b2, b2⟫_ℝ)⁻¹ • b2 = _
    rw [hM2, hb2]
    exact tube_native_a2 hr hq
  have hH : ∀ X Z : R3 × R3, H X Z = D X Z := fun X Z => by
    show fderiv ℝ (fderiv ℝ (tubePhase M e0 a σ)) (Y + tubeRadius M e0 a σ Y • ω, Y) X Z -
      ell (Gamma1 X.1 Z.1, Gamma2 X.2 Z.2) = _
    rw [hG1, hG2, hDf, Prod.mk_zero_zero, map_zero, sub_zero]
  refine ⟨hl1, hl2, fun v1 v2 h1 h2 h3 h4 => ?_⟩
  rw [hM1, ha1] at h1
  rw [hM1, hM1, ha1] at h2
  rw [hM2, ha2] at h3
  rw [hM2, hM2, ha2] at h4
  obtain ⟨hv1, hv1ω⟩ := tube_native_v1_constraints hr hω h1 h2
  obtain ⟨hv2q, hv2⟩ := tube_native_v2_constraints hr hq h3 h4
  rw [hH, hH, ha1, ha2, tube_phase_hessian_sum hDe]
  exact hE v1 v2 hv1 hv1ω hv2q hv2

/-- N7: the N6 scalar at `V1 = r⁻¹ v`, `V2 = r⁻¹ w` is `r⁻²` times T12's flat form `E` minus the two actual
`r D²r` corrections at `u = ‖ω+b‖⁻² (ω+b)` and `w`. -/
theorem tube_native_scalar_scale {ω b v w : R3} {r k s e0 : ℝ} (d : R3 →L[ℝ] ℝ) (hr : r ≠ 0)
    (hd : ∀ U : R3, k * d U = ⟪b, U⟫_ℝ) :
    ⟪r⁻¹ • ω + -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b), r⁻¹ • ω + -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)⟫_ℝ +
        ⟪r⁻¹ • v - r⁻¹ • w, r⁻¹ • v - r⁻¹ • w⟫_ℝ -
        (k * d (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b))) ^ 2 - (k * d (r⁻¹ • w)) ^ 2 -
        r * (s * d (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)) ^ 2 +
          k * (2 * e0 * ((-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)) 0 ^ 2 +
            (-((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b)) 1 ^ 2)) +
          s * d (r⁻¹ • w) ^ 2 + k * (2 * e0 * ((r⁻¹ • w) 0 ^ 2 + (r⁻¹ • w) 1 ^ 2))) =
      (r ^ 2)⁻¹ * ((‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
          ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2) -
        r * (s * d ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) ^ 2 +
          k * (2 * e0 * (((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) 0 ^ 2 + ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) 1 ^ 2)) +
          s * d w ^ 2 + k * (2 * e0 * (w 0 ^ 2 + w 1 ^ 2)))) := by
  have hQ : -((r * ‖ω + b‖ ^ 2)⁻¹) • (ω + b) = -(r⁻¹ • ((‖ω + b‖ ^ 2)⁻¹ • (ω + b))) := by
    rw [smul_smul, mul_inv, neg_smul]
  generalize (‖ω + b‖ ^ 2)⁻¹ • (ω + b) = u at hQ ⊢
  have hP : r⁻¹ • ω + -(r⁻¹ • u) = r⁻¹ • (ω - u) := by rw [smul_sub, sub_eq_add_neg]
  rw [hQ, hP, ← smul_sub r⁻¹ v w]
  simp only [real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← hd u, ← hd w]
  simp only [map_neg, map_smul, smul_eq_mul, PiLp.neg_apply, PiLp.smul_apply]
  field_simp

/-- N8: with `m0` chosen from T12 by `amin, Bb, ε` BEFORE `σ, e0, T0` and the tube data, the literal native
identity-metric `ProductHessianStrictAt` holds for the SAME `tubePhase` whenever the actual `r D²r`
corrections stay below `m0`. -/
theorem tube_native_strict_of_margin {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ (M e0 a σ : ℝ) (Y ω : R3), 0 < tubeHeight M e0 Y →
      0 < tubeRadius M e0 a σ Y → ‖ω‖ = 1 →
      amin ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ≤ Bb →
      ε ≤ ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ε ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y + (2 : ℝ) • ω‖ →
      (∀ w : R3, ⟪w, ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y⟫_ℝ = 0 →
        ‖w‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 →
        tubeRadius M e0 a σ Y *
          (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) * tubeHeightDeriv e0 Y
            ((‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)) ^ 2 +
          a * (1 + σ) * tubeHeight M e0 Y ^ σ * (2 * e0 *
            (((‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)) 0 ^ 2 +
            ((‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹ •
              (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)) 1 ^ 2)) +
          a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) * tubeHeightDeriv e0 Y w ^ 2 +
          a * (1 + σ) * tubeHeight M e0 Y ^ σ * (2 * e0 * (w 0 ^ 2 + w 1 ^ 2))) < m0) →
      ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
        (tubePhase M e0 a σ) := by
  obtain ⟨m0, hm0, hT12⟩ := tube_flat_form_compact_min (Bb := Bb) ham hε
  refine ⟨m0, hm0, fun M e0 a σ Y ω ht hr hω hb1 hb2 hn1 hn2 hcorr => ?_⟩
  have hq : ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y ≠ 0 := fun h => by
    rw [h, norm_zero] at hn1
    linarith
  refine tube_native_strict_of_form M e0 a σ ht hω rfl rfl rfl rfl hr.ne' hq
    (fun v1 v2 hv1 hv1ω hv2q hv2 => ?_)
  have hd : ∀ U : R3, a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y U =
      ⟪(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y, U⟫_ℝ := fun U => by
    rw [tubeHeightDeriv_eq_inner, real_inner_smul_left]
  have e1 : v1 = (tubeRadius M e0 a σ Y)⁻¹ • (tubeRadius M e0 a σ Y • v1) :=
    (inv_smul_smul₀ hr.ne' v1).symm
  have e2 : v2 = (tubeRadius M e0 a σ Y)⁻¹ • (tubeRadius M e0 a σ Y • v2) :=
    (inv_smul_smul₀ hr.ne' v2).symm
  have hscale := tube_native_scalar_scale (ω := ω) (v := tubeRadius M e0 a σ Y • v1)
    (w := tubeRadius M e0 a σ Y • v2) (s := a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1))
    (e0 := e0) (tubeHeightDeriv e0 Y) hr.ne' hd
  rw [← e1, ← e2] at hscale
  rw [hscale]
  have hE := hT12 ω (tubeRadius M e0 a σ Y • v1)
    ((a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y) (tubeRadius M e0 a σ Y • v2)
    hω hv1ω hv1 hv2q hv2 hb1 hb2 hn1 hn2
  have hC := hcorr (tubeRadius M e0 a σ Y • v2) hv2q hv2
  have hr2 : 0 < (tubeRadius M e0 a σ Y ^ 2)⁻¹ := inv_pos.mpr (pow_pos hr 2)
  exact mul_pos hr2 (by linarith)

/-- N9: one actual `r D²r` correction term is at most `σ Bb² L² + 4 e0 Bb R L²`. -/
theorem tube_corr_term_le {r s k e0 σ D X0 X1 nb nx Bb R L : ℝ}
    (hrs : r * s = σ / (1 + σ) * k ^ 2) (hσ : 0 ≤ σ) (he0 : 0 ≤ e0) (hk0 : 0 ≤ k) (hkB : k ≤ Bb)
    (hr0 : 0 ≤ r) (hrR : r ≤ R) (hD : |k * D| ≤ nb * nx) (hnb : 0 ≤ nb) (hnbB : nb ≤ Bb)
    (hnx : 0 ≤ nx) (hnxL : nx ≤ L) (hX : X0 ^ 2 + X1 ^ 2 ≤ 2 * nx ^ 2) :
    r * (s * D ^ 2 + k * (2 * e0 * (X0 ^ 2 + X1 ^ 2))) ≤
      σ * Bb ^ 2 * L ^ 2 + 4 * e0 * Bb * R * L ^ 2 := by
  have hB0 : 0 ≤ Bb := hnb.trans hnbB
  have hL0 : 0 ≤ L := hnx.trans hnxL
  have h1 : r * (s * D ^ 2) = σ / (1 + σ) * (k * D) ^ 2 := by
    rw [← mul_assoc, hrs]
    ring
  have hkd : |k * D| ≤ Bb * L := hD.trans (mul_le_mul hnbB hnxL hnx hB0)
  have h2 : (k * D) ^ 2 ≤ (Bb * L) ^ 2 := sq_le_sq' (abs_le.mp hkd).1 (abs_le.mp hkd).2
  have h3 : σ / (1 + σ) ≤ σ := div_le_self hσ (by linarith)
  have h5 : σ / (1 + σ) * (k * D) ^ 2 ≤ σ * (Bb * L) ^ 2 := mul_le_mul h3 h2 (sq_nonneg _) hσ
  have hnx2 : nx ^ 2 ≤ L ^ 2 := by nlinarith
  have h6 : X0 ^ 2 + X1 ^ 2 ≤ 2 * L ^ 2 := hX.trans (by linarith)
  have hX0 : 0 ≤ X0 ^ 2 + X1 ^ 2 := by positivity
  have h7 : r * (k * (2 * e0 * (X0 ^ 2 + X1 ^ 2))) ≤ R * (Bb * (2 * e0 * (2 * L ^ 2))) :=
    mul_le_mul hrR (mul_le_mul hkB (mul_le_mul_of_nonneg_left h6 (by positivity))
      (by positivity) hB0) (by positivity) (hr0.trans hrR)
  have h8 : r * (s * D ^ 2 + k * (2 * e0 * (X0 ^ 2 + X1 ^ 2))) =
      r * (s * D ^ 2) + r * (k * (2 * e0 * (X0 ^ 2 + X1 ^ 2))) := mul_add _ _ _
  have h9 : σ * (Bb * L) ^ 2 = σ * Bb ^ 2 * L ^ 2 := by ring
  have h10 : R * (Bb * (2 * e0 * (2 * L ^ 2))) = 4 * e0 * Bb * R * L ^ 2 := by ring
  linarith

/-- N10: quantified placement. `m0` from T12/N8, then `σ0, e00` chosen after `m0`, give the literal native
identity-metric `ProductHessianStrictAt` for the SAME `tubePhase` on the whole T12 parameter domain. -/
theorem tube_native_strict_placement {amin Bb ε R : ℝ} (ham : 0 < amin) (hε : 0 < ε)
    (hB : 0 ≤ Bb) (hR : 0 ≤ R) :
    ∃ m0 σ0 e00 : ℝ, 0 < m0 ∧ 0 < σ0 ∧ 0 < e00 ∧ ∀ (M e0 a σ : ℝ) (Y ω : R3),
      0 ≤ σ → σ ≤ σ0 → 0 ≤ e0 → e0 ≤ e00 → 0 < tubeHeight M e0 Y →
      0 < tubeRadius M e0 a σ Y → tubeRadius M e0 a σ Y ≤ R → ‖ω‖ = 1 →
      amin ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ≤ Bb →
      ε ≤ ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ε ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y + (2 : ℝ) • ω‖ →
      ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
        (tubePhase M e0 a σ) := by
  obtain ⟨m0, hm0, hN8⟩ := tube_native_strict_of_margin (Bb := Bb) ham hε
  refine ⟨m0, m0 / (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)), m0 / (16 * (Bb * R * ε⁻¹ ^ 2 + 1)), hm0,
    by positivity, by positivity, ?_⟩
  intro M e0 a σ Y ω hσ hσ0 he0 he00 ht hr hrR hω hb1 hb2 hn1 hn2
  refine hN8 M e0 a σ Y ω ht hr hω hb1 hb2 hn1 hn2 (fun w hw hw1 => ?_)
  have hg2 : tubeHeightGrad e0 Y 2 = 1 := by simp [tubeHeightGrad]
  have hg1 : 1 ≤ ‖tubeHeightGrad e0 Y‖ := by
    have h := abs_coord_le_norm (tubeHeightGrad e0 Y) 2
    rw [hg2, abs_one] at h
    exact h
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have ha : 0 < a := by
    by_contra h
    have h' : a * tubeHeight M e0 Y ^ (1 + σ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) htp.le
    exact (not_lt.mpr h') hr
  have hk0 : 0 ≤ a * (1 + σ) * tubeHeight M e0 Y ^ σ := by
    have := Real.rpow_nonneg ht.le σ
    have h1σ : 0 ≤ 1 + σ := by linarith
    positivity
  have hkn : ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ =
      a * (1 + σ) * tubeHeight M e0 Y ^ σ * ‖tubeHeightGrad e0 Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hkB : a * (1 + σ) * tubeHeight M e0 Y ^ σ ≤ Bb := by
    rw [hkn] at hb2
    nlinarith
  have hrs : tubeRadius M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1)) =
      σ / (1 + σ) * (a * (1 + σ) * tubeHeight M e0 Y ^ σ) ^ 2 :=
    (tube_radius_hessian_coeffs (a := a) ht hσ).1
  have hd : ∀ U : R3, a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y U =
      ⟪(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y, U⟫_ℝ := fun U => by
    rw [tubeHeightDeriv_eq_inner, real_inner_smul_left]
  have hL : ∀ X : R3,
      ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 →
      ‖X‖ ≤ ε⁻¹ := fun X hX => by
    rw [← one_div, le_div_iff₀ hε]
    calc ‖X‖ * ε ≤ ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ :=
          mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
      _ = 1 := hX
  have hq0 : 0 < ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ :=
    lt_of_lt_of_le hε hn1
  have hu1 : ‖(‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹ •
      (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)‖ *
      ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    first | (field_simp; done) | (field_simp; ring)
  have hterm : ∀ X : R3,
      ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 →
      tubeRadius M e0 a σ Y *
        (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) * tubeHeightDeriv e0 Y X ^ 2 +
          a * (1 + σ) * tubeHeight M e0 Y ^ σ * (2 * e0 * (X 0 ^ 2 + X 1 ^ 2))) ≤
        σ * Bb ^ 2 * ε⁻¹ ^ 2 + 4 * e0 * Bb * R * ε⁻¹ ^ 2 := fun X hX =>
    tube_corr_term_le hrs hσ he0 hk0 hkB hr.le hrR (by rw [hd]; exact abs_real_inner_le_norm _ _)
      (norm_nonneg _) hb2 (norm_nonneg _) (hL X hX) (tube_horizontal_sq_le X)
  have h1 := hterm _ hu1
  have h2 := hterm w hw1
  have hσm : σ * (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp hσ0
  have hem : e0 * (16 * (Bb * R * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp he00
  nlinarith

/-- N11: the actual tube vector `b = a(1+σ)t^σ g_Y` satisfies `amin ≤ ‖b‖` (T6, since `g_Y 2 = 1`). -/
theorem tube_b_norm_lower_actual {M e0 a σ amin : ℝ} {Y : R3} (hσ : 0 ≤ σ)
    (ht : 1 ≤ tubeHeight M e0 Y) (ham : 0 ≤ amin) (ha : amin ≤ a) :
    amin ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ := by
  have hg2 : tubeHeightGrad e0 Y 2 = 1 := by simp [tubeHeightGrad]
  have h := tube_b_norm_lower (g := tubeHeightGrad e0 Y) hg2 hσ ht ham ha
  have hc : (1 + σ) * a * tubeHeight M e0 Y ^ σ = a * (1 + σ) * tubeHeight M e0 Y ^ σ := by ring
  rwa [hc] at h

/-- N12: outside the literal coarse seed, with `σ ≤ 1` and `‖g_Y‖ ≤ 2`, the actual `b` has `‖b‖ ≤ 4/c0`. -/
theorem tube_b_norm_upper_unseeded {M e0 a σ c0 : ℝ} {Y ω : R3} (hM : 0 ≤ M) (he0 : 0 ≤ e0)
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 < c0) (ht : 0 < tubeHeight M e0 Y)
    (hω : ‖ω‖ = 1) (hg : ‖tubeHeightGrad e0 Y‖ ≤ 2)
    (hout : ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
      c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖)) :
    ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ≤ 4 / c0 := by
  have hts : 0 ≤ tubeHeight M e0 Y ^ σ := Real.rpow_nonneg ht.le σ
  have hr : tubeRadius M e0 a σ Y = a * tubeHeight M e0 Y ^ σ * tubeHeight M e0 Y := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one]
    ring
  have hA0 : 0 ≤ a * tubeHeight M e0 Y ^ σ := mul_nonneg ha hts
  have hr0 : 0 ≤ tubeRadius M e0 a σ Y := by
    rw [hr]
    exact mul_nonneg hA0 ht.le
  have hn : ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ = tubeRadius M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [hn, not_lt] at hout
  have hY : c0 * tubeRadius M e0 a σ Y ≤ Y 2 := hout.trans (min_le_right _ _)
  have htY : Y 2 ≤ tubeHeight M e0 Y := by
    have h := mul_nonneg he0 (add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1)))
    simp only [tubeHeight]
    linarith
  rw [hr] at hY
  have hcA : c0 * (a * tubeHeight M e0 Y ^ σ) ≤ 1 := by
    have h : c0 * (a * tubeHeight M e0 Y ^ σ) * tubeHeight M e0 Y ≤ 1 * tubeHeight M e0 Y := by
      linarith
    exact le_of_mul_le_mul_right h ht
  have hAc : a * tubeHeight M e0 Y ^ σ ≤ 1 / c0 := by
    rw [le_div_iff₀ hc0]
    linarith
  have hk0 : 0 ≤ a * (1 + σ) * tubeHeight M e0 Y ^ σ := by
    have h1σ : 0 ≤ 1 + σ := by linarith
    positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hk : a * (1 + σ) * tubeHeight M e0 Y ^ σ ≤ 2 * (1 / c0) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ) hA0]
  calc a * (1 + σ) * tubeHeight M e0 Y ^ σ * ‖tubeHeightGrad e0 Y‖ ≤ 2 * (1 / c0) * 2 :=
        mul_le_mul hk hg (norm_nonneg _) (by positivity)
    _ = 4 / c0 := by ring

/-- N13: with `e0 (Y₀² + Y₁²) ≤ T0` and `e0 T0 ≤ 3/4`, the actual gradient has `‖g_Y‖ ≤ 2`. -/
theorem tube_grad_norm_le_two {e0 T0 : ℝ} {Y : R3} (he0 : 0 ≤ e0)
    (hY : e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0) (hT : e0 * T0 ≤ 3 / 4) :
    ‖tubeHeightGrad e0 Y‖ ≤ 2 := by
  have hsq : ‖tubeHeightGrad e0 Y‖ ^ 2 = (2 * e0 * Y 0) ^ 2 + (2 * e0 * Y 1) ^ 2 + 1 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      Fin.sum_univ_three]
    simp only [tubeHeightGrad, Real.norm_eq_abs, sq_abs]
    simp
  have h := mul_le_mul_of_nonneg_left hY he0
  have h4 : (2 * e0 * Y 0) ^ 2 + (2 * e0 * Y 1) ^ 2 ≤ 3 := by nlinarith
  nlinarith [norm_nonneg (tubeHeightGrad e0 Y)]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

/-! ## v059: eps-separations from the original coarse seed (N14-N15 of REPORT.md) -/
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- N15: with `e0 (Y₀² + Y₁²) ≤ T0` and `4 (e0 T0) ≤ η²`, the actual gradient has `‖g_Y - e₂‖ ≤ η`. -/
theorem tube_grad_near_e2 {e0 T0 η : ℝ} {Y : R3} (he0 : 0 ≤ e0) (hη : 0 ≤ η)
    (hY : e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0) (hT : 4 * (e0 * T0) ≤ η ^ 2) :
    ‖tubeHeightGrad e0 Y - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ η := by
  have hsq : ‖tubeHeightGrad e0 Y - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ^ 2 =
      (2 * e0 * Y 0) ^ 2 + (2 * e0 * Y 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
      Fin.sum_univ_three]
    simp only [tubeHeightGrad, Real.norm_eq_abs, sq_abs]
    first | (simp [EuclideanSpace.single_apply]; done) | (simp [EuclideanSpace.single_apply]; ring)
  have h := mul_le_mul_of_nonneg_left hY he0
  have hid : (2 * e0 * Y 0) ^ 2 + (2 * e0 * Y 1) ^ 2 = 4 * (e0 * (e0 * (Y 0 ^ 2 + Y 1 ^ 2))) := by
    ring
  have hle : ‖tubeHeightGrad e0 Y - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ^ 2 ≤ η ^ 2 := by
    rw [hsq, hid]
    linarith
  have h2 := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hη] at h2

/-- N14: outside the literal coarse seed, the actual `b = a(1+σ)t^σ g_Y = ((1+σ)(r/t)) g_Y` stays `ε`-separated
from `-ω` and `-2ω` (contraposition of T19/T20 through T10). -/
theorem tube_sep_of_unseeded {M e0 a σ c0 η ε : ℝ} {Y ω : R3} (hM : 0 < M) (he0 : 0 ≤ e0)
    (ht : 0 < tubeHeight M e0 Y) (hr : 0 < tubeRadius M e0 a σ Y) (hω : ‖ω‖ = 1)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    (hc0 : 13 * η ≤ c0)
    (hge : ‖tubeHeightGrad e0 Y - EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ η)
    (hout : ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
      c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖)) :
    ε < ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ∧
      ε < ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y + (2 : ℝ) • ω‖ := by
  have ht0 : tubeHeight M e0 Y ≠ 0 := ht.ne'
  have hk : a * (1 + σ) * tubeHeight M e0 Y ^ σ =
      (1 + σ) * (tubeRadius M e0 a σ Y / tubeHeight M e0 Y) := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one,
      mul_comm (tubeHeight M e0 Y) (tubeHeight M e0 Y ^ σ), ← mul_assoc, mul_div_cancel_right₀ _ ht0]
    ring
  have hy : Y 2 < tubeHeight M e0 Y := by
    have h := mul_nonneg he0 (add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1)))
    simp only [tubeHeight]
    linarith
  have hg2 : tubeHeightGrad e0 Y 2 = 1 := by simp [tubeHeightGrad]
  have hn : ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ = tubeRadius M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have hseed : Y 2 + tubeRadius M e0 a σ Y * ω 2 < c0 * tubeRadius M e0 a σ Y → False :=
    fun h => by
      apply hout
      rw [tube_min_height hr.le, hn]
      have hm := mul_le_mul_of_nonneg_left (min_le_left (ω 2) 0) hr.le
      linarith
  constructor
  · by_contra h
    rw [not_lt, add_comm ω, hk] at h
    exact hseed (tube_excluded_one_low hω hg2 hge hr ht hσ0 hσ hε hη (by linarith) hc0 hy h)
  · by_contra h
    rw [not_lt, hk] at h
    exact hseed (tube_excluded_two_low hω hg2 hge hr ht hσ0 hσ hε hη hη10 (by linarith) hy h)

/-- N16: on the capped sweep `1 ≤ t ≤ U`, `0 ≤ a ≤ 2/c0 + 1`, `0 ≤ σ ≤ 1`, the actual radius is `≤ (2/c0+1) U²`. -/
theorem tube_radius_le_sweep {M e0 a σ c0 U : ℝ} {Y : R3} (hc0 : 0 < c0) (ht1 : 1 ≤ tubeHeight M e0 Y)
    (htU : tubeHeight M e0 Y ≤ U) (ha0 : 0 ≤ a) (ha : a ≤ 2 / c0 + 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    tubeRadius M e0 a σ Y ≤ (2 / c0 + 1) * U ^ 2 := by
  have h1 : tubeHeight M e0 Y ^ (1 + σ) ≤ tubeHeight M e0 Y ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have h2 : tubeHeight M e0 Y ^ (2 : ℝ) ≤ U ^ 2 := by
    rw [Real.rpow_two]
    nlinarith
  have hc : 0 ≤ 2 / c0 + 1 := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  rw [tubeRadius]
  exact mul_le_mul ha (h1.trans h2) (Real.rpow_nonneg (by linarith) _) hc

/-- N17: capped-sweep assembly. After the fixed `c0, η, d, U`, choose `σ`, then `T0`, then `e0`; every
unseeded capped-sweep point gives the literal identity-metric `ProductHessianStrictAt` for the SAME `tubePhase`. -/
theorem tube_native_strict_sweep {c0 η d U : ℝ} (hc0 : 0 < c0) (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hU : 1 ≤ U) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 1 < c0 * min 1 (d / (2 * U ^ 2)) * T0 ^ σ ∧
      0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
      ∀ (M a : ℝ) (Y ω : R3), 0 < M → ‖ω‖ = 1 → 1 ≤ tubeHeight M e0 Y →
        tubeHeight M e0 Y ≤ U → e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0 →
        min 1 (d / (2 * U ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖) →
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
          (tubePhase M e0 a σ) := by
  have hU2 : 0 < 2 * U ^ 2 := by positivity
  have ham : 0 < min 1 (d / (2 * U ^ 2)) := lt_min one_pos (div_pos hd hU2)
  have hB : 0 ≤ 4 / c0 := div_nonneg (by norm_num) hc0.le
  have hc2 : 0 ≤ 2 / c0 + 1 := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  have hR : 0 ≤ (2 / c0 + 1) * U ^ 2 := mul_nonneg hc2 (sq_nonneg U)
  obtain ⟨m0, σ0, e00, _hm0, hσ0, he00, hP⟩ :=
    tube_native_strict_placement (Bb := 4 / c0) (R := (2 / c0 + 1) * U ^ 2) ham hη hB hR
  obtain ⟨σ, hσpos, hσσ0, hση, hσ1⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ σ0 ∧ σ ≤ η ∧ σ ≤ 1 := by
    have hm : 0 < min (min σ0 η) 1 := lt_min (lt_min hσ0 hη) one_pos
    have h1 : min (min σ0 η) 1 ≤ σ0 := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min σ0 η) 1 ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min σ0 η) 1 ≤ 1 := min_le_right _ _
    exact ⟨min (min σ0 η) 1 / 2, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T0, hT0pos, hT0⟩ : ∃ T0 : ℝ, 0 < T0 ∧ 1 < c0 * min 1 (d / (2 * U ^ 2)) * T0 ^ σ := by
    have hca : 0 < c0 * min 1 (d / (2 * U ^ 2)) := mul_pos hc0 ham
    have hBp : 0 < 1 / (c0 * min 1 (d / (2 * U ^ 2))) := one_div_pos.mpr hca
    have hp : 0 ≤ (1 / (c0 * min 1 (d / (2 * U ^ 2)))) ^ (1 / σ) := Real.rpow_nonneg hBp.le _
    refine ⟨(1 / (c0 * min 1 (d / (2 * U ^ 2)))) ^ (1 / σ) + 1, by linarith, ?_⟩
    have hlt := Real.rpow_lt_rpow hp (lt_add_one ((1 / (c0 * min 1 (d / (2 * U ^ 2)))) ^ (1 / σ)))
      hσpos
    rw [← Real.rpow_mul hBp.le, one_div_mul_cancel hσpos.ne', Real.rpow_one] at hlt
    have h1 : c0 * min 1 (d / (2 * U ^ 2)) * (1 / (c0 * min 1 (d / (2 * U ^ 2)))) = 1 :=
      mul_one_div_cancel hca.ne'
    have h2 := mul_lt_mul_of_pos_left hlt hca
    linarith
  obtain ⟨e0, he0pos, he0e00, he0T, he0η, he0B⟩ : ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ e00 ∧ e0 * T0 ≤ 3 / 4 ∧
      4 * (e0 * T0) ≤ η ^ 2 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) := by
    have hq1 : 0 < 3 / (4 * T0) := div_pos (by norm_num) (by linarith)
    have hq2 : 0 < η ^ 2 / (4 * T0) := div_pos (by positivity) (by linarith)
    have hq3 : 0 < 1 / ((4 / c0) ^ 2 + 1) := by positivity
    have hm0 : 0 < min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) :=
      lt_min (lt_min he00 hq1) (lt_min hq2 hq3)
    have h1 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤ e00 :=
      (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        3 / (4 * T0) := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        η ^ 2 / (4 * T0) := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        1 / ((4 / c0) ^ 2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h2
    have h3' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h3
    refine ⟨min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) / 2,
      by linarith, by linarith, ?_, ?_, by linarith⟩
    · nlinarith
    · nlinarith
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hT0, he0pos, he0B, ?_⟩
  intro M a Y ω hM hω ht1 htU hYT ha1 ha2 hout
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have ha0 : 0 < a := ham.trans_le ha1
  have hr : 0 < tubeRadius M e0 a σ Y := by
    rw [tubeRadius]
    exact mul_pos ha0 (Real.rpow_pos_of_pos ht _)
  have hge := tube_grad_near_e2 he0pos.le hη.le hYT he0η
  have hg2 := tube_grad_norm_le_two he0pos.le hYT he0T
  have hsep := tube_sep_of_unseeded hM he0pos.le ht hr hω hσpos.le hση le_rfl hη hη10 hc0η hge hout
  have hlow := tube_b_norm_lower_actual (M := M) (e0 := e0) (Y := Y) hσpos.le ht1 ham.le ha1
  have hup := tube_b_norm_upper_unseeded hM.le he0pos.le ha0.le hσpos.le hσ1 hc0 ht hω hg2 hout
  have hrR := tube_radius_le_sweep hc0 ht1 htU ha0.le ha2 hσpos.le hσ1
  exact hP M e0 a σ Y ω hσpos.le hσσ0 he0pos.le he0e00 ht hr hrR hω hlow hup hsep.1.le hsep.2.le

/-- N18: N10 with the N8/N9 choices exposed: `m0, σ0` are chosen without `R`; only `e00` depends on `R`. -/
theorem tube_native_strict_placement_uniform {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε)
    (hB : 0 ≤ Bb) :
    ∃ m0 σ0 : ℝ, 0 < m0 ∧ 0 < σ0 ∧ ∀ R : ℝ, 0 ≤ R → ∃ e00 : ℝ, 0 < e00 ∧ ∀ (M e0 a σ : ℝ) (Y ω : R3),
      0 ≤ σ → σ ≤ σ0 → 0 ≤ e0 → e0 ≤ e00 → 0 < tubeHeight M e0 Y →
      0 < tubeRadius M e0 a σ Y → tubeRadius M e0 a σ Y ≤ R → ‖ω‖ = 1 →
      amin ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ≤ Bb →
      ε ≤ ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ →
      ε ≤ ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y + (2 : ℝ) • ω‖ →
      ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
        (tubePhase M e0 a σ) := by
  obtain ⟨m0, hm0, hN8⟩ := tube_native_strict_of_margin (Bb := Bb) ham hε
  refine ⟨m0, m0 / (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)), hm0, by positivity, fun R hR =>
    ⟨m0 / (16 * (Bb * R * ε⁻¹ ^ 2 + 1)), by positivity, ?_⟩⟩
  intro M e0 a σ Y ω hσ hσ0 he0 he00 ht hr hrR hω hb1 hb2 hn1 hn2
  refine hN8 M e0 a σ Y ω ht hr hω hb1 hb2 hn1 hn2 (fun w hw hw1 => ?_)
  have hg2 : tubeHeightGrad e0 Y 2 = 1 := by simp [tubeHeightGrad]
  have hg1 : 1 ≤ ‖tubeHeightGrad e0 Y‖ := by
    have h := abs_coord_le_norm (tubeHeightGrad e0 Y) 2
    rw [hg2, abs_one] at h
    exact h
  have htp : 0 < tubeHeight M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have ha : 0 < a := by
    by_contra h
    have h' : a * tubeHeight M e0 Y ^ (1 + σ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) htp.le
    exact (not_lt.mpr h') hr
  have hk0 : 0 ≤ a * (1 + σ) * tubeHeight M e0 Y ^ σ := by
    have := Real.rpow_nonneg ht.le σ
    have h1σ : 0 ≤ 1 + σ := by linarith
    positivity
  have hkn : ‖(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ =
      a * (1 + σ) * tubeHeight M e0 Y ^ σ * ‖tubeHeightGrad e0 Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hkB : a * (1 + σ) * tubeHeight M e0 Y ^ σ ≤ Bb := by
    rw [hkn] at hb2
    nlinarith
  have hrs : tubeRadius M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1)) =
      σ / (1 + σ) * (a * (1 + σ) * tubeHeight M e0 Y ^ σ) ^ 2 :=
    (tube_radius_hessian_coeffs (a := a) ht hσ).1
  have hd : ∀ U : R3, a * (1 + σ) * tubeHeight M e0 Y ^ σ * tubeHeightDeriv e0 Y U =
      ⟪(a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y, U⟫_ℝ := fun U => by
    rw [tubeHeightDeriv_eq_inner, real_inner_smul_left]
  have hL : ∀ X : R3,
      ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 →
      ‖X‖ ≤ ε⁻¹ := fun X hX => by
    rw [← one_div, le_div_iff₀ hε]
    calc ‖X‖ * ε ≤ ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ :=
          mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
      _ = 1 := hX
  have hq0 : 0 < ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ :=
    lt_of_lt_of_le hε hn1
  have hu1 : ‖(‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ ^ 2)⁻¹ •
      (ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y)‖ *
      ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    first | (field_simp; done) | (field_simp; ring)
  have hterm : ∀ X : R3,
      ‖X‖ * ‖ω + (a * (1 + σ) * tubeHeight M e0 Y ^ σ) • tubeHeightGrad e0 Y‖ = 1 →
      tubeRadius M e0 a σ Y *
        (a * (1 + σ) * σ * tubeHeight M e0 Y ^ (σ - 1) * tubeHeightDeriv e0 Y X ^ 2 +
          a * (1 + σ) * tubeHeight M e0 Y ^ σ * (2 * e0 * (X 0 ^ 2 + X 1 ^ 2))) ≤
        σ * Bb ^ 2 * ε⁻¹ ^ 2 + 4 * e0 * Bb * R * ε⁻¹ ^ 2 := fun X hX =>
    tube_corr_term_le hrs hσ he0 hk0 hkB hr.le hrR (by rw [hd]; exact abs_real_inner_le_norm _ _)
      (norm_nonneg _) hb2 (norm_nonneg _) (hL X hX) (tube_horizontal_sq_le X)
  have h1 := hterm _ hu1
  have h2 := hterm w hw1
  have hσm : σ * (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp hσ0
  have hem : e0 * (16 * (Bb * R * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp he00
  nlinarith

/-- N19: uniform sweep order `c0, η, amin → σ → T0 → U → e0`; the height cap `U` (hence `R`) may be chosen
after `T0`. The level floor `amin` is a free positive datum here (its link to target separations is not claimed). -/
theorem tube_native_strict_sweep_uniform {c0 η amin : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (ham : 0 < amin) :
    ∃ σ T0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧ 1 < c0 * amin * T0 ^ σ ∧
      ∀ U : ℝ, 1 ≤ U → ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
        ∀ (M a : ℝ) (Y ω : R3), 0 < M → ‖ω‖ = 1 → 1 ≤ tubeHeight M e0 Y →
          tubeHeight M e0 Y ≤ U → e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0 →
          amin ≤ a → a ≤ 2 / c0 + 1 →
          ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
            c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖) →
          ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
            (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
            (tubePhase M e0 a σ) := by
  have hB : 0 ≤ 4 / c0 := div_nonneg (by norm_num) hc0.le
  have hc2 : 0 ≤ 2 / c0 + 1 := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  obtain ⟨m0, σ0, _hm0, hσ0, hP⟩ := tube_native_strict_placement_uniform (Bb := 4 / c0) ham hη hB
  obtain ⟨σ, hσpos, hσσ0, hση, hσ1⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ σ0 ∧ σ ≤ η ∧ σ ≤ 1 := by
    have hm : 0 < min (min σ0 η) 1 := lt_min (lt_min hσ0 hη) one_pos
    have h1 : min (min σ0 η) 1 ≤ σ0 := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min σ0 η) 1 ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min σ0 η) 1 ≤ 1 := min_le_right _ _
    exact ⟨min (min σ0 η) 1 / 2, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T0, hT0pos, hT0⟩ : ∃ T0 : ℝ, 0 < T0 ∧ 1 < c0 * amin * T0 ^ σ := by
    have hca : 0 < c0 * amin := mul_pos hc0 ham
    have hBp : 0 < 1 / (c0 * amin) := one_div_pos.mpr hca
    have hp : 0 ≤ (1 / (c0 * amin)) ^ (1 / σ) := Real.rpow_nonneg hBp.le _
    refine ⟨(1 / (c0 * amin)) ^ (1 / σ) + 1, by linarith, ?_⟩
    have hlt := Real.rpow_lt_rpow hp (lt_add_one ((1 / (c0 * amin)) ^ (1 / σ))) hσpos
    rw [← Real.rpow_mul hBp.le, one_div_mul_cancel hσpos.ne', Real.rpow_one] at hlt
    have h1 : c0 * amin * (1 / (c0 * amin)) = 1 := mul_one_div_cancel hca.ne'
    have h2 := mul_lt_mul_of_pos_left hlt hca
    linarith
  refine ⟨σ, T0, hσpos, hση, hσ1, hT0pos, hT0, fun U hU => ?_⟩
  have hR : 0 ≤ (2 / c0 + 1) * U ^ 2 := mul_nonneg hc2 (sq_nonneg U)
  obtain ⟨e00, he00, hQ⟩ := hP ((2 / c0 + 1) * U ^ 2) hR
  obtain ⟨e0, he0pos, he0e00, he0T, he0η, he0B⟩ : ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ e00 ∧ e0 * T0 ≤ 3 / 4 ∧
      4 * (e0 * T0) ≤ η ^ 2 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) := by
    have hq1 : 0 < 3 / (4 * T0) := div_pos (by norm_num) (by linarith)
    have hq2 : 0 < η ^ 2 / (4 * T0) := div_pos (by positivity) (by linarith)
    have hq3 : 0 < 1 / ((4 / c0) ^ 2 + 1) := by positivity
    have hm0 : 0 < min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) :=
      lt_min (lt_min he00 hq1) (lt_min hq2 hq3)
    have h1 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤ e00 :=
      (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        3 / (4 * T0) := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        η ^ 2 / (4 * T0) := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        1 / ((4 / c0) ^ 2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h2
    have h3' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h3
    refine ⟨min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) / 2,
      by linarith, by linarith, ?_, ?_, by linarith⟩
    · nlinarith
    · nlinarith
  refine ⟨e0, he0pos, he0B, ?_⟩
  intro M a Y ω hM hω ht1 htU hYT ha1 ha2 hout
  have ht : 0 < tubeHeight M e0 Y := by linarith
  have ha0 : 0 < a := ham.trans_le ha1
  have hr : 0 < tubeRadius M e0 a σ Y := by
    rw [tubeRadius]
    exact mul_pos ha0 (Real.rpow_pos_of_pos ht _)
  have hge := tube_grad_near_e2 he0pos.le hη.le hYT he0η
  have hg2 := tube_grad_norm_le_two he0pos.le hYT he0T
  have hsep := tube_sep_of_unseeded hM he0pos.le ht hr hω hσpos.le hση le_rfl hη hη10 hc0η hge hout
  have hlow := tube_b_norm_lower_actual (M := M) (e0 := e0) (Y := Y) hσpos.le ht1 ham.le ha1
  have hup := tube_b_norm_upper_unseeded hM.le he0pos.le ha0.le hσpos.le hσ1 hc0 ht hω hg2 hout
  have hrR := tube_radius_le_sweep hc0 ht1 htU ha0.le ha2 hσpos.le hσ1
  exact hQ M e0 a σ Y ω hσpos.le hσσ0 he0pos.le he0e00 ht hr hrR hω hlow hup hsep.1.le hsep.2.le

/-- N20: source order. The TARGET height cap `Ut` fixes `amin` (T21) before `σ`; the SWEEP height cap is `T0`
itself, chosen after `σ`; `e0` is chosen last. -/
theorem tube_native_strict_sweep_targets {c0 η d Ut : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hUt : 1 ≤ Ut) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 1 < c0 * min 1 (d / (2 * Ut ^ 2)) * T0 ^ σ ∧
      0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
      (∀ D t : ℝ, d ≤ D → 1 ≤ t → t ≤ Ut → min 1 (d / (2 * Ut ^ 2)) < D / t ^ (1 + σ)) ∧
      ∀ (M a : ℝ) (Y ω : R3), 0 < M → ‖ω‖ = 1 → 1 ≤ tubeHeight M e0 Y →
        tubeHeight M e0 Y ≤ T0 → e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0 →
        min 1 (d / (2 * Ut ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖) →
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
          (tubePhase M e0 a σ) := by
  have hU2 : 0 < 2 * Ut ^ 2 := by positivity
  have ham : 0 < min 1 (d / (2 * Ut ^ 2)) := lt_min one_pos (div_pos hd hU2)
  obtain ⟨σ, T0, hσpos, hση, hσ1, _hT0pos, hT0, hU⟩ :=
    tube_native_strict_sweep_uniform hc0 hη hη10 hc0η ham
  obtain ⟨e0, he0pos, he0B, hS⟩ := hU (max 1 T0) (le_max_left _ _)
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hT0, he0pos, he0B,
    fun D t hdD ht1 htU => tube_target_level_gt hd hdD ht1 htU hσpos.le hσ1, ?_⟩
  intro M a Y ω hM hω ht1 htT hYT ha1 ha2 hout
  exact hS M a Y ω hM hω ht1 (htT.trans (le_max_right _ _)) hYT ha1 ha2 hout

/-- N21: on the source base `y_n ≥ -B-1`, `M > B+3`, `t ≤ T0`, one has `1 ≤ t` and `e0 |y'|² ≤ T0`. -/
theorem tube_base_height {M e0 B T0 : ℝ} {Y : R3} (he0 : 0 ≤ e0) (hM : B + 3 < M)
    (hy : -B - 1 ≤ Y 2) (htT : tubeHeight M e0 Y ≤ T0) :
    1 ≤ tubeHeight M e0 Y ∧ e0 * (Y 0 ^ 2 + Y 1 ^ 2) ≤ T0 := by
  have h := mul_nonneg he0 (add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1)))
  simp only [tubeHeight] at htT ⊢
  constructor <;> linarith

/-- N22: targets with `y_n ≤ B`, `|y'|² ≤ B²` and `e0 ≤ 1` lie at height `t ≤ M + B + B²`. -/
theorem tube_target_height_le {M e0 B : ℝ} {Y : R3} (he0 : 0 ≤ e0) (he01 : e0 ≤ 1)
    (hy : Y 2 ≤ B) (hh : Y 0 ^ 2 + Y 1 ^ 2 ≤ B ^ 2) :
    tubeHeight M e0 Y ≤ M + B + B ^ 2 := by
  have hh0 : 0 ≤ Y 0 ^ 2 + Y 1 ^ 2 := add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1))
  have h := mul_le_mul he01 hh hh0 zero_le_one
  simp only [tubeHeight]
  linarith

/-- N23: N20 in the source base coordinates `y_n ≥ -B-1`, `M > B+3`, with target cap `Ut = M + B + B²`. -/
theorem tube_native_strict_sweep_base {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      (∀ (D : ℝ) (Y : R3), d ≤ D → -B - 1 ≤ Y 2 → Y 2 ≤ B → Y 0 ^ 2 + Y 1 ^ 2 ≤ B ^ 2 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) < D / tubeHeight M e0 Y ^ (1 + σ)) ∧
      ∀ (a : ℝ) (Y ω : R3), ‖ω‖ = 1 → -B - 1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) <
          c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖) →
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (Y + tubeRadius M e0 a σ Y • ω) Y
          (tubePhase M e0 a σ) := by
  have hUt : 1 ≤ M + B + B ^ 2 := by
    have := sq_nonneg B
    linarith
  obtain ⟨σ, T0, e0, hσpos, hση, hσ1, hT0, he0pos, he0B, htgt, hS⟩ :=
    tube_native_strict_sweep_targets hc0 hη hη10 hc0η hd hUt
  have h1 : 1 / ((4 / c0) ^ 2 + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [sq_nonneg (4 / c0)]
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hT0, he0pos, he0B.trans h1, ?_, ?_⟩
  · intro D Y hdD hy1 hy2 hh
    exact htgt D _ hdD (tube_base_height (T0 := tubeHeight M e0 Y) he0pos.le hM hy1 le_rfl).1
      (tube_target_height_le he0pos.le (he0B.trans h1) hy2 hh)
  · intro a Y ω hω hy htT ha1 ha2 hout
    obtain ⟨ht1, hYT⟩ := tube_base_height he0pos.le hM hy htT
    have hM0 : 0 < M := by linarith
    exact hS M a Y ω hM0 hω ht1 htT hYT ha1 ha2 hout

/-- N24: the whole `a ≥ 2/c0 + 1` level lies in the literal coarse seed (T8). -/
theorem tube_amax_level_in_seed {M e0 a σ c0 : ℝ} {Y ω : R3} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight M e0 Y) (hσ : 0 ≤ σ) (ha : 2 / c0 + 1 ≤ a) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) < c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ := by
  have ha0 : 0 ≤ a := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  have hr0 : 0 ≤ tubeRadius M e0 a σ Y := by
    rw [tubeRadius]
    exact mul_nonneg ha0 (Real.rpow_nonneg (by linarith) _)
  have hn : ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ = tubeRadius M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h2 : tubeHeight M e0 Y < c0 * tubeRadius M e0 a σ Y := tube_amax_level_seeded hc0 ht1 hσ ha
  have hy : Y 2 ≤ tubeHeight M e0 Y := by
    have h := mul_nonneg he0 (add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1)))
    simp only [tubeHeight]
    linarith
  have h1 : min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) ≤ Y 2 := min_le_right _ _
  rw [hn]
  linarith

/-- N25: the bottom base face `y_n < 0` lies in the literal coarse seed for every positive radius. -/
theorem tube_bottom_face_in_seed {M e0 a σ c0 : ℝ} {Y ω : R3} (hc0 : 0 < c0)
    (hr : 0 < tubeRadius M e0 a σ Y) (hy : Y 2 < 0) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) < c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ := by
  have hn : ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ = tubeRadius M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have h1 : min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) ≤ Y 2 := min_le_right _ _
  have h2 := mul_pos hc0 hr
  rw [hn]
  linarith

/-- N26: where `1 < c0 amin t^σ` (the top face `t = T0`, by T9), every level `a ≥ amin` lies in the literal
coarse seed. -/
theorem tube_top_face_in_seed {M e0 a σ c0 amin : ℝ} {Y ω : R3} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht : 0 < tubeHeight M e0 Y) (hamin : 0 ≤ amin) (ham : amin ≤ a)
    (htop : 1 < c0 * amin * tubeHeight M e0 Y ^ σ) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) < c0 * ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ := by
  have hts : 0 ≤ tubeHeight M e0 Y ^ σ := Real.rpow_nonneg ht.le σ
  have hr : tubeRadius M e0 a σ Y = a * tubeHeight M e0 Y ^ σ * tubeHeight M e0 Y := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one]
    ring
  have ha0 : 0 ≤ a := hamin.trans ham
  have hr0 : 0 ≤ tubeRadius M e0 a σ Y := by
    rw [hr]
    exact mul_nonneg (mul_nonneg ha0 hts) ht.le
  have hn : ‖(Y + tubeRadius M e0 a σ Y • ω) - Y‖ = tubeRadius M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hge : c0 * amin * tubeHeight M e0 Y ^ σ ≤ c0 * a * tubeHeight M e0 Y ^ σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ham hc0.le) hts
  have hlt := mul_lt_mul_of_pos_right (htop.trans_le hge) ht
  have hy : Y 2 ≤ tubeHeight M e0 Y := by
    have h := mul_nonneg he0 (add_nonneg (sq_nonneg (Y 0)) (sq_nonneg (Y 1)))
    simp only [tubeHeight]
    linarith
  have h1 : min ((Y + tubeRadius M e0 a σ Y • ω) 2) (Y 2) ≤ Y 2 := min_le_right _ _
  have hc : c0 * tubeRadius M e0 a σ Y = c0 * a * tubeHeight M e0 Y ^ σ * tubeHeight M e0 Y := by
    rw [hr]
    ring
  rw [hn, hc]
  linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace Topology

/-- N27: an operator within `1/2` of the identity has quadratic form between `‖v‖²/2` and `3‖v‖²/2`. -/
theorem metric_near_one_quad_bounds {M : R3 →L[ℝ] R3}
    (hM : ‖M - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) (v : R3) :
    ‖v‖ ^ 2 / 2 ≤ ⟪M v, v⟫_ℝ ∧ ⟪M v, v⟫_ℝ ≤ 3 / 2 * ‖v‖ ^ 2 := by
  have hsplit : ⟪M v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(M - ContinuousLinearMap.id ℝ R3) v, v⟫_ℝ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_sub_left,
      real_inner_self_eq_norm_sq]
    ring
  have h2 := abs_real_inner_le_norm ((M - ContinuousLinearMap.id ℝ R3) v) v
  have h3 := (M - ContinuousLinearMap.id ℝ R3).le_opNorm v
  have h4 : ‖(M - ContinuousLinearMap.id ℝ R3) v‖ * ‖v‖ ≤ 1 / 2 * ‖v‖ * ‖v‖ :=
    mul_le_mul_of_nonneg_right (h3.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg v)))
      (norm_nonneg v)
  have h5 := abs_le.mp (h2.trans h4)
  have hsq : ‖v‖ ^ 2 = ‖v‖ * ‖v‖ := sq _
  constructor <;> linarith [h5.1, h5.2]

/-- N28: a characteristic vector (`⟪M v,v⟫ = ⟪M a,a⟫`) for an operator within `1/2` of the identity
satisfies `‖v‖² ≤ 3‖a‖²`; this is the fixed compact fiber for the bad-set projection. -/
theorem char_vector_norm_sq_le {M : R3 →L[ℝ] R3}
    (hM : ‖M - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) {v a : R3}
    (hva : ⟪M v, v⟫_ℝ = ⟪M a, a⟫_ℝ) : ‖v‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 := by
  have hv := (metric_near_one_quad_bounds hM v).1
  have ha := (metric_near_one_quad_bounds hM a).2
  linarith

/-- N29: the actual normalized normal `⟪M b,b⟫⁻¹ • b` satisfies `‖a‖ ‖b‖ ≤ 2` near the identity. -/
theorem normal_norm_mul_le_two {M : R3 →L[ℝ] R3}
    (hM : ‖M - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) {b : R3} (hb : b ≠ 0) :
    ‖(⟪M b, b⟫_ℝ)⁻¹ • b‖ * ‖b‖ ≤ 2 := by
  have hq := (metric_near_one_quad_bounds hM b).1
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hb2 : 0 < ‖b‖ ^ 2 / 2 := by positivity
  have hqpos : 0 < ⟪M b, b⟫_ℝ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hqpos, inv_mul_eq_div,
    div_mul_eq_mul_div, div_le_iff₀ hqpos]
  have hsq : ‖b‖ ^ 2 = ‖b‖ * ‖b‖ := sq _
  linarith

/-- N30: every actual characteristic vector for the normal `a = ⟪M b,b⟫⁻¹ • b` satisfies
`‖v‖² ‖b‖² ≤ 12` near the identity. -/
theorem char_vector_norm_sq_mul_le {M : R3 →L[ℝ] R3}
    (hM : ‖M - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) {a b v : R3} (hb : b ≠ 0)
    (ha : a = (⟪M b, b⟫_ℝ)⁻¹ • b) (hv : ⟪M v, v⟫_ℝ = ⟪M a, a⟫_ℝ) :
    ‖v‖ ^ 2 * ‖b‖ ^ 2 ≤ 12 := by
  have h1 := char_vector_norm_sq_le hM hv
  have h2 : ‖a‖ * ‖b‖ ≤ 2 := ha ▸ normal_norm_mul_le_two hM hb
  have h3 : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  have h4 : (‖a‖ * ‖b‖) ^ 2 ≤ 4 := by nlinarith
  calc ‖v‖ ^ 2 * ‖b‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 * ‖b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 3 * (‖a‖ * ‖b‖) ^ 2 := by ring
    _ ≤ 12 := by linarith

/-- N31: a closed bad set avoiding `{p0} × K` with `K` compact avoids `U × K` for some
neighborhood `U` of `p0`. -/
theorem eventually_forall_not_bad_of_isClosed {D V : Type*} [TopologicalSpace D]
    [TopologicalSpace V] {K : Set V} (hK : IsCompact K) {bad : D → V → Prop}
    (hbad : IsClosed {z : D × V | bad z.1 z.2}) {p0 : D} (h0 : ∀ v ∈ K, ¬ bad p0 v) :
    ∀ᶠ p in 𝓝 p0, ∀ v ∈ K, ¬ bad p v :=
  hK.eventually_forall_of_forall_eventually (P := fun p v => ¬ bad p v) fun v hv =>
    show {z : D × V | bad z.1 z.2}ᶜ ∈ 𝓝 (p0, v) from hbad.isOpen_compl.mem_nhds (h0 v hv)

/-- N32: if moreover every bad vector eventually lies in the compact fiber `K`, then eventually
no vector at all is bad (actual universal positivity, not a truncated statement). -/
theorem eventually_forall_not_bad_of_fiber {D V : Type*} [TopologicalSpace D]
    [TopologicalSpace V] {K : Set V} (hK : IsCompact K) {bad : D → V → Prop}
    (hbad : IsClosed {z : D × V | bad z.1 z.2}) {p0 : D} (h0 : ∀ v ∈ K, ¬ bad p0 v)
    (hfib : ∀ᶠ p in 𝓝 p0, ∀ v, bad p v → v ∈ K) :
    ∀ᶠ p in 𝓝 p0, ∀ v, ¬ bad p v :=
  ((eventually_forall_not_bad_of_isClosed hK hbad h0).and hfib).mono
    fun _ h v hv => h.1 v (h.2 v hv) hv

/-- N33: local goodness near every `(0, q)`, `q` in a compact sweep `Q`, gives ONE `λ0 > 0` serving
all `λ ∈ (0, λ0]` and all `q ∈ Q`. -/
theorem exists_uniform_lambda0 {S : Type*} [TopologicalSpace S] {Q : Set S} (hQ : IsCompact Q)
    {good : ℝ → S → Prop} (h : ∀ q ∈ Q, ∀ᶠ z : ℝ × S in 𝓝 ((0 : ℝ), q), good z.1 z.2) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ q ∈ Q, good lam q := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (hQ.eventually_forall_of_forall_eventually h)
  refine ⟨ε / 2, by positivity, ?_⟩
  intro lam hl hle q hq
  have hd : dist lam 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hl]
    linarith
  exact hball hd q hq

/-- N34: the compact-fiber openness (N32) at every `(0, q)` combined with N33: one `λ0` after which
no vector is bad, uniformly on the compact sweep. -/
theorem exists_uniform_lambda0_of_fiber {S V : Type*} [TopologicalSpace S] [TopologicalSpace V]
    {Q : Set S} (hQ : IsCompact Q) {bad : ℝ × S → V → Prop}
    (hbad : IsClosed {z : (ℝ × S) × V | bad z.1 z.2}) (K : S → Set V)
    (hK : ∀ q ∈ Q, IsCompact (K q)) (h0 : ∀ q ∈ Q, ∀ v ∈ K q, ¬ bad ((0 : ℝ), q) v)
    (hfib : ∀ q ∈ Q, ∀ᶠ p in 𝓝 ((0 : ℝ), q), ∀ v, bad p v → v ∈ K q) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ q ∈ Q, ∀ v, ¬ bad (lam, q) v :=
  exists_uniform_lambda0 hQ (good := fun lam s => ∀ v, ¬ bad (lam, s) v) fun q hq =>
    eventually_forall_not_bad_of_fiber (hK q hq) hbad (h0 q hq) (hfib q hq)

/-- N35: near the identity, with `β ≤ ‖b‖`, every actual characteristic vector lies in the closed
ball of radius `4/β`. -/
theorem char_vector_mem_closedBall {M : R3 →L[ℝ] R3}
    (hM : ‖M - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) {β : ℝ} (hβ : 0 < β) {a b v : R3}
    (hb : β ≤ ‖b‖) (ha : a = (⟪M b, b⟫_ℝ)⁻¹ • b) (hv : ⟪M v, v⟫_ℝ = ⟪M a, a⟫_ℝ) :
    v ∈ Metric.closedBall (0 : R3) (4 / β) := by
  have hb0 : b ≠ 0 := norm_pos_iff.mp (hβ.trans_le hb)
  have h12 := char_vector_norm_sq_mul_le hM hb0 ha hv
  have hβb : β ^ 2 ≤ ‖b‖ ^ 2 := pow_le_pow_left₀ hβ.le hb 2
  have hx : (‖v‖ * β) ^ 2 ≤ 12 := by
    calc (‖v‖ * β) ^ 2 = ‖v‖ ^ 2 * β ^ 2 := by ring
      _ ≤ ‖v‖ ^ 2 * ‖b‖ ^ 2 := mul_le_mul_of_nonneg_left hβb (by positivity)
      _ ≤ 12 := h12
  have hx0 : 0 ≤ ‖v‖ * β := by positivity
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hβ]
  nlinarith

/-- N36: both actual characteristic vectors lie in the product fiber of radius `4/β`. -/
theorem char_pair_mem_fiber {M1 M2 : R3 →L[ℝ] R3}
    (hM1 : ‖M1 - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2)
    (hM2 : ‖M2 - ContinuousLinearMap.id ℝ R3‖ ≤ 1 / 2) {β : ℝ} (hβ : 0 < β)
    {a1 b1 v1 a2 b2 v2 : R3} (hb1 : β ≤ ‖b1‖) (hb2 : β ≤ ‖b2‖)
    (ha1 : a1 = (⟪M1 b1, b1⟫_ℝ)⁻¹ • b1) (ha2 : a2 = (⟪M2 b2, b2⟫_ℝ)⁻¹ • b2)
    (hv1 : ⟪M1 v1, v1⟫_ℝ = ⟪M1 a1, a1⟫_ℝ) (hv2 : ⟪M2 v2, v2⟫_ℝ = ⟪M2 a2, a2⟫_ℝ) :
    (v1, v2) ∈ Metric.closedBall (0 : R3) (4 / β) ×ˢ Metric.closedBall (0 : R3) (4 / β) :=
  ⟨char_vector_mem_closedBall hM1 hβ hb1 ha1 hv1, char_vector_mem_closedBall hM2 hβ hb2 ha2 hv2⟩

/-- N37: the product fiber is compact. -/
theorem char_pair_fiber_isCompact (ρ : ℝ) :
    IsCompact (Metric.closedBall (0 : R3) ρ ×ˢ Metric.closedBall (0 : R3) ρ) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

/-- N38: continuity at `p0` of the metric operators (equal to the identity there) and of the
nonzero inverse-metric gradients gives the compact-fiber hypothesis of N34 near `p0`. -/
theorem eventually_fiber_of_continuousAt {D : Type*} [TopologicalSpace D] {p0 : D}
    (M1 M2 : D → R3 →L[ℝ] R3) (b1 b2 : D → R3) (hM1 : ContinuousAt M1 p0)
    (hM2 : ContinuousAt M2 p0) (hM10 : M1 p0 = ContinuousLinearMap.id ℝ R3)
    (hM20 : M2 p0 = ContinuousLinearMap.id ℝ R3) (hb1 : ContinuousAt b1 p0)
    (hb2 : ContinuousAt b2 p0) (hb10 : b1 p0 ≠ 0) (hb20 : b2 p0 ≠ 0) {bad : D → R3 × R3 → Prop}
    (hlen : ∀ p v, bad p v →
      ⟪M1 p v.1, v.1⟫_ℝ = ⟪M1 p ((⟪M1 p (b1 p), b1 p⟫_ℝ)⁻¹ • b1 p),
        (⟪M1 p (b1 p), b1 p⟫_ℝ)⁻¹ • b1 p⟫_ℝ ∧
      ⟪M2 p v.2, v.2⟫_ℝ = ⟪M2 p ((⟪M2 p (b2 p), b2 p⟫_ℝ)⁻¹ • b2 p),
        (⟪M2 p (b2 p), b2 p⟫_ℝ)⁻¹ • b2 p⟫_ℝ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ p in 𝓝 p0, ∀ v, bad p v →
      v ∈ Metric.closedBall (0 : R3) (4 / β) ×ˢ Metric.closedBall (0 : R3) (4 / β) := by
  have hn1 : 0 < ‖b1 p0‖ := norm_pos_iff.mpr hb10
  have hn2 : 0 < ‖b2 p0‖ := norm_pos_iff.mpr hb20
  have hmin : 0 < min ‖b1 p0‖ ‖b2 p0‖ := lt_min hn1 hn2
  have hl1 : min ‖b1 p0‖ ‖b2 p0‖ / 2 < ‖b1 p0‖ := by
    have := min_le_left ‖b1 p0‖ ‖b2 p0‖
    linarith
  have hl2 : min ‖b1 p0‖ ‖b2 p0‖ / 2 < ‖b2 p0‖ := by
    have := min_le_right ‖b1 p0‖ ‖b2 p0‖
    linarith
  refine ⟨min ‖b1 p0‖ ‖b2 p0‖ / 2, by linarith, ?_⟩
  have e1 := hM1.eventually (Metric.closedBall_mem_nhds (M1 p0) (by norm_num : (0 : ℝ) < 1 / 2))
  have e2 := hM2.eventually (Metric.closedBall_mem_nhds (M2 p0) (by norm_num : (0 : ℝ) < 1 / 2))
  have e3 := hb1.norm.eventually (lt_mem_nhds hl1)
  have e4 := hb2.norm.eventually (lt_mem_nhds hl2)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4 v hv
  rw [dist_eq_norm, hM10] at h1
  rw [dist_eq_norm, hM20] at h2
  obtain ⟨l1, l2⟩ := hlen p v hv
  exact char_pair_mem_fiber h1 h2 (by linarith) h3.le h4.le rfl rfl l1 l2

/-- N39: for continuous metric, normal and quadratic-form fields, the set of violating
characteristic pairs of the product test is closed. -/
theorem productStrict_bad_isClosed {D : Type*} [TopologicalSpace D]
    {M1 M2 : D → R3 →L[ℝ] R3} {a1 a2 : D → R3}
    {Hf : D → (R3 × R3) →L[ℝ] (R3 × R3) →L[ℝ] ℝ} (hM1 : Continuous M1) (hM2 : Continuous M2)
    (ha1 : Continuous a1) (ha2 : Continuous a2) (hH : Continuous Hf) :
    IsClosed {z : D × (R3 × R3) |
      ⟪M1 z.1 z.2.1, a1 z.1⟫_ℝ = 0 ∧ ⟪M1 z.1 z.2.1, z.2.1⟫_ℝ = ⟪M1 z.1 (a1 z.1), a1 z.1⟫_ℝ ∧
      ⟪M2 z.1 z.2.2, a2 z.1⟫_ℝ = 0 ∧ ⟪M2 z.1 z.2.2, z.2.2⟫_ℝ = ⟪M2 z.1 (a2 z.1), a2 z.1⟫_ℝ ∧
      Hf z.1 (a1 z.1, -a2 z.1) (a1 z.1, -a2 z.1) + Hf z.1 z.2 z.2 ≤ 0} := by
  have cM1 : Continuous fun z : D × (R3 × R3) => M1 z.1 := hM1.comp continuous_fst
  have cM2 : Continuous fun z : D × (R3 × R3) => M2 z.1 := hM2.comp continuous_fst
  have ca1 : Continuous fun z : D × (R3 × R3) => a1 z.1 := ha1.comp continuous_fst
  have ca2 : Continuous fun z : D × (R3 × R3) => a2 z.1 := ha2.comp continuous_fst
  have cH : Continuous fun z : D × (R3 × R3) => Hf z.1 := hH.comp continuous_fst
  have cv1 : Continuous fun z : D × (R3 × R3) => z.2.1 := continuous_snd.fst
  have cv2 : Continuous fun z : D × (R3 × R3) => z.2.2 := continuous_snd.snd
  have cv : Continuous fun z : D × (R3 × R3) => z.2 := continuous_snd
  have cA : Continuous fun z : D × (R3 × R3) => (a1 z.1, -a2 z.1) := ca1.prodMk ca2.neg
  have c0 : Continuous fun _ : D × (R3 × R3) => (0 : ℝ) := continuous_const
  have e1 := isClosed_eq ((cM1.clm_apply cv1).inner (𝕜 := ℝ) ca1) c0
  have e2 := isClosed_eq ((cM1.clm_apply cv1).inner (𝕜 := ℝ) cv1)
    ((cM1.clm_apply ca1).inner (𝕜 := ℝ) ca1)
  have e3 := isClosed_eq ((cM2.clm_apply cv2).inner (𝕜 := ℝ) ca2) c0
  have e4 := isClosed_eq ((cM2.clm_apply cv2).inner (𝕜 := ℝ) cv2)
    ((cM2.clm_apply ca2).inner (𝕜 := ℝ) ca2)
  have e5 := isClosed_le (((cH.clm_apply cA).clm_apply cA).add ((cH.clm_apply cv).clm_apply cv)) c0
  simp only [Set.setOf_and]
  exact e1.inter (e2.inter (e3.inter (e4.inter e5)))

/-- N40: N31 with closedness of the bad set required only over a neighborhood `C` of `p0`. -/
theorem eventually_forall_not_bad_of_isClosed_local {D V : Type*} [TopologicalSpace D]
    [TopologicalSpace V] {K : Set V} (hK : IsCompact K) {bad : D → V → Prop} {p0 : D}
    {C : Set D} (hC : C ∈ 𝓝 p0) (hbad : IsClosed {z : D × V | z.1 ∈ C ∧ bad z.1 z.2})
    (h0 : ∀ v ∈ K, ¬ bad p0 v) :
    ∀ᶠ p in 𝓝 p0, ∀ v ∈ K, ¬ bad p v :=
  hK.eventually_forall_of_forall_eventually (P := fun p v => ¬ bad p v) fun v hv => by
    have h1 : {z : D × V | z.1 ∈ C ∧ bad z.1 z.2}ᶜ ∈ 𝓝 (p0, v) :=
      hbad.isOpen_compl.mem_nhds fun h => h0 v hv h.2
    have h2 : ∀ᶠ z : D × V in 𝓝 (p0, v), z.1 ∈ C :=
      (continuous_fst.tendsto (p0, v)).eventually (p := fun y => y ∈ C) hC
    filter_upwards [h1, h2] with z hz1 hz2
    exact fun hb => hz1 ⟨hz2, hb⟩

/-- N41: N32 with closedness of the bad set required only over a neighborhood `C` of `p0`. -/
theorem eventually_forall_not_bad_of_fiber_local {D V : Type*} [TopologicalSpace D]
    [TopologicalSpace V] {K : Set V} (hK : IsCompact K) {bad : D → V → Prop} {p0 : D}
    {C : Set D} (hC : C ∈ 𝓝 p0) (hbad : IsClosed {z : D × V | z.1 ∈ C ∧ bad z.1 z.2})
    (h0 : ∀ v ∈ K, ¬ bad p0 v) (hfib : ∀ᶠ p in 𝓝 p0, ∀ v, bad p v → v ∈ K) :
    ∀ᶠ p in 𝓝 p0, ∀ v, ¬ bad p v :=
  ((eventually_forall_not_bad_of_isClosed_local hK hC hbad h0).and hfib).mono
    fun _ h v hv => h.1 v (h.2 v hv) hv

/-- N42: N34 with closedness of the bad set required only over neighborhoods of each `(0, q)`. -/
theorem exists_uniform_lambda0_of_fiber_local {S V : Type*} [TopologicalSpace S]
    [TopologicalSpace V] {Q : Set S} (hQ : IsCompact Q) {bad : ℝ × S → V → Prop}
    (C : S → Set (ℝ × S)) (hC : ∀ q ∈ Q, C q ∈ 𝓝 ((0 : ℝ), q))
    (hbad : ∀ q ∈ Q, IsClosed {z : (ℝ × S) × V | z.1 ∈ C q ∧ bad z.1 z.2}) (K : S → Set V)
    (hK : ∀ q ∈ Q, IsCompact (K q)) (h0 : ∀ q ∈ Q, ∀ v ∈ K q, ¬ bad ((0 : ℝ), q) v)
    (hfib : ∀ q ∈ Q, ∀ᶠ p in 𝓝 ((0 : ℝ), q), ∀ v, bad p v → v ∈ K q) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ q ∈ Q, ∀ v, ¬ bad (lam, q) v :=
  exists_uniform_lambda0 hQ (good := fun lam s => ∀ v, ¬ bad (lam, s) v) fun q hq =>
    eventually_forall_not_bad_of_fiber_local (hK q hq) (hC q hq) (hbad q hq) (h0 q hq) (hfib q hq)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology

/-- N43: the scaled metric operator `(λ, X) ↦ M_g(λ • X)` is jointly smooth, including at `λ = 0`. -/
theorem scaled_metricOperatorField_contDiff (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ fun p : ℝ × R3 => MetricOperator.metricOperatorField g (p.1 • p.2) :=
  (MetricOperator.contDiff_metricOperatorField g hg).comp (contDiff_fst.smul contDiff_snd)

/-- N44: if `g 0 = 1`, the scaled metric operator is the identity at `λ = 0`. -/
theorem scaled_metricOperatorField_zero (g : MatrixField) (hg0 : g 0 = 1) (X : R3) :
    MetricOperator.metricOperatorField g ((0 : ℝ) • X) = ContinuousLinearMap.id ℝ R3 := by
  ext1 Z
  rw [zero_smul]
  change MetricOperator.matrixOperatorMap (g 0) Z = Z
  rw [hg0]
  exact euclidean_matrixOperator_one Z

/-- N45: for the actual source metrics, both scaled metric operators are continuous and equal the
identity at every base point `(0, X)` (the metric hypotheses of N38). -/
theorem actual_scaled_metric_base (S : KnownSideSourceData) :
    Continuous (fun p : ℝ × R3 => MetricOperator.metricOperatorField S.g1 (p.1 • p.2)) ∧
    Continuous (fun p : ℝ × R3 => MetricOperator.metricOperatorField S.g2 (p.1 • p.2)) ∧
    ∀ X : R3, MetricOperator.metricOperatorField S.g1 ((0 : ℝ) • X) = ContinuousLinearMap.id ℝ R3 ∧
      MetricOperator.metricOperatorField S.g2 ((0 : ℝ) • X) = ContinuousLinearMap.id ℝ R3 :=
  ⟨(scaled_metricOperatorField_contDiff S.g1 S.g1_admissible).continuous,
    (scaled_metricOperatorField_contDiff S.g2 S.g2_admissible).continuous,
    fun X => ⟨scaled_metricOperatorField_zero S.g1 S.g1_origin X,
      scaled_metricOperatorField_zero S.g2 S.g2_origin X⟩⟩

/-- N46: the scaled inverse metric `(λ, X) ↦ (M_g(λ • X))⁻¹` is jointly smooth, including at `λ = 0`. -/
theorem scaled_inverseMetricField_contDiff (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ContDiff ℝ ∞ fun p : ℝ × R3 =>
      ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) (p.1 • p.2) :=
  (ConnectionError.contDiff_inverseMetricField _ (MetricOperator.contDiff_metricOperatorField g hg)
    (MetricOperator.isUnit_metricOperatorField g hg)).comp (contDiff_fst.smul contDiff_snd)

/-- N47: if `g 0 = 1`, the scaled inverse metric is the identity at `λ = 0`. -/
theorem scaled_inverseMetricField_zero (g : MatrixField) (hg0 : g 0 = 1) (X : R3) :
    ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) ((0 : ℝ) • X) =
      ContinuousLinearMap.id ℝ R3 := by
  change Ring.inverse (MetricOperator.metricOperatorField g ((0 : ℝ) • X)) = _
  rw [scaled_metricOperatorField_zero g hg0 X]
  exact Ring.inverse_one (M₀ := R3 →L[ℝ] R3)

/-- N48: the actual inverse-metric covector `(M_g(s p))⁻¹ (G p)` is continuous, and at a base point
with `s p0 = 0` it equals the Euclidean gradient `G p0` (so it is nonzero when `G p0` is). -/
theorem scaled_inverse_covector_base {D : Type*} [TopologicalSpace D] (g : MatrixField)
    (hg : IsAdmissibleMetric g) (hg0 : g 0 = 1) {s G : D → R3} (hs : Continuous s)
    (hG : Continuous G) {p0 : D} (hs0 : s p0 = 0) :
    Continuous (fun p => ConnectionError.inverseMetricField
      (MetricOperator.metricOperatorField g) (s p) (G p)) ∧
    ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g) (s p0) (G p0) = G p0 := by
  refine ⟨((ConnectionError.contDiff_inverseMetricField _
    (MetricOperator.contDiff_metricOperatorField g hg)
    (MetricOperator.isUnit_metricOperatorField g hg)).continuous.comp hs).clm_apply hG, ?_⟩
  have h := scaled_inverseMetricField_zero g hg0 0
  rw [zero_smul] at h
  rw [hs0, h]
  rfl

/-- N49: for `σ ≥ 0` the actual tube radius `(a, Y) ↦ a t(Y)^(1+σ)` is jointly continuous. -/
theorem tubeRadius_continuous (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous fun p : ℝ × R3 => tubeRadius M e0 p.1 σ p.2 := by
  have ht : Continuous (tubeHeight M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt M e0 Y).continuousAt
  show Continuous fun p : ℝ × R3 => p.1 * tubeHeight M e0 p.2 ^ (1 + σ)
  exact continuous_fst.mul ((ht.comp continuous_snd).rpow_const fun _ => Or.inr (by linarith))

/-- N50: the actual tube endpoint `(a, Y, ω) ↦ Y + r_a(Y) ω` is jointly continuous. -/
theorem tubeEndpoint_continuous (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous fun p : ℝ × R3 × R3 => p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2 :=
  continuous_snd.fst.add
    (((tubeRadius_continuous M e0 σ hσ).comp (continuous_fst.prodMk continuous_snd.fst)).smul
      continuous_snd.snd)

/-- N51: the literal N23 unseeded sweep set of `(a, Y, ω)` is closed. -/
theorem tubeSweep_isClosed (M e0 σ c0 B T0 amin amax : ℝ) (hσ : 0 ≤ σ) :
    IsClosed {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
      amin ≤ p.1 ∧ p.1 ≤ amax ∧
      c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} := by
  have ht : Continuous (tubeHeight M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt M e0 Y).continuousAt
  have hE := tubeEndpoint_continuous M e0 σ hσ
  have hY : Continuous fun p : ℝ × R3 × R3 => p.2.1 := continuous_snd.fst
  have hY2 : Continuous fun p : ℝ × R3 × R3 => p.2.1 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp hY
  have hX2 : Continuous fun p : ℝ × R3 × R3 => (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.comp hE
  have hc : ∀ c : ℝ, Continuous fun _ : ℝ × R3 × R3 => c := fun c => continuous_const
  have ha : Continuous fun p : ℝ × R3 × R3 => p.1 := continuous_fst
  have e1 : IsClosed {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1} :=
    isClosed_eq (continuous_norm.comp continuous_snd.snd) (hc 1)
  have e2 : IsClosed {p : ℝ × R3 × R3 | -B - 1 ≤ p.2.1 2} := isClosed_le (hc _) hY2
  have e3 : IsClosed {p : ℝ × R3 × R3 | tubeHeight M e0 p.2.1 ≤ T0} :=
    isClosed_le (ht.comp hY) (hc _)
  have e4 : IsClosed {p : ℝ × R3 × R3 | amin ≤ p.1} := isClosed_le (hc _) ha
  have e5 : IsClosed {p : ℝ × R3 × R3 | p.1 ≤ amax} := isClosed_le ha (hc _)
  have e6 : IsClosed {p : ℝ × R3 × R3 |
      c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} :=
    isClosed_le ((hc c0).mul (hE.sub hY).norm) (hX2.min hY2)
  simp only [Set.setOf_and]
  exact e1.inter (e2.inter (e3.inter (e4.inter (e5.inter e6))))

/-- N52: for `e0 > 0` the literal N23 unseeded sweep set of `(a, Y, ω)` is compact. -/
theorem tubeSweep_isCompact (M e0 σ c0 B T0 amin amax : ℝ) (hσ : 0 ≤ σ) (he0 : 0 < e0) :
    IsCompact {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
      amin ≤ p.1 ∧ p.1 ≤ amax ∧
      c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} := by
  refine Metric.isCompact_of_isClosed_isBounded (tubeSweep_isClosed M e0 σ c0 B T0 amin amax hσ) ?_
  set C : ℝ := |B| + 1 + |T0| + |M| with hC
  set S : ℝ := Real.sqrt ((T0 - M + B + 1) / e0 + C ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × R3 × R3))
    (r := |amin| + |amax| + S + 1)).subset ?_
  rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, -⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hamin := neg_abs_le amin
  have hamax := le_abs_self amax
  have h0min := abs_nonneg amin
  have h0max := abs_nonneg amax
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by simp only at ha1 ⊢; linarith, by simp only at ha2 ⊢; linarith⟩
  · simp only at hY2 hT ⊢
    unfold tubeHeight at hT
    have hs0 : 0 ≤ e0 * (Y 0 ^ 2 + Y 1 ^ 2) := by positivity
    have h1 : Y 0 ^ 2 + Y 1 ^ 2 ≤ (T0 - M + B + 1) / e0 := by
      rw [le_div_iff₀ he0]
      linarith [mul_comm e0 (Y 0 ^ 2 + Y 1 ^ 2)]
    have hT0 := le_abs_self T0
    have hM0 := neg_abs_le M
    have hT1 := abs_nonneg T0
    have hM1 := abs_nonneg M
    have hB0 := le_abs_self B
    have hB1 := abs_nonneg B
    have h2 : Y 2 ^ 2 ≤ C ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hn : ‖Y‖ = Real.sqrt (Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs]
    have hY : ‖Y‖ ≤ S := by
      rw [hn, hS]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  · simp only at hw ⊢
    linarith

/-- N53: N23's constants make the literal sweep set `Q` compact, and N23's identity-data strictness
holds at every point of `Q`. -/
theorem tube_native_strict_sweep_set {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ 0 < e0 ∧
      IsCompact {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)} ∧
      ∀ p ∈ {p : ℝ × R3 × R3 | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 2 ∧ tubeHeight M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2) 2) (p.2.1 2)},
        ProductHessianStrictAt (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (p.2.1 + tubeRadius M e0 p.1 σ p.2.1 • p.2.2)
          p.2.1 (tubePhase M e0 p.1 σ) := by
  obtain ⟨σ, T0, e0, hσ, -, -, -, he0, -, -, hS⟩ :=
    tube_native_strict_sweep_base hc0 hη hη10 hc0η hd hB hM
  refine ⟨σ, T0, e0, hσ, he0, tubeSweep_isCompact M e0 σ c0 B T0 _ _ hσ.le he0, ?_⟩
  rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, hsep⟩
  exact hS a Y w hw hY2 hT ha1 ha2 (not_lt.2 hsep)

/-- N54: at every sweep point the positive-height set `{t > 0}` is a neighborhood. -/
theorem tubeSweep_height_pos_nhds {M e0 B T0 : ℝ} (he0 : 0 ≤ e0) (hM : B + 3 < M)
    {p : ℝ × R3 × R3} (hy : -B - 1 ≤ p.2.1 2) (htT : tubeHeight M e0 p.2.1 ≤ T0) :
    {q : ℝ × R3 × R3 | 0 < tubeHeight M e0 q.2.1} ∈ 𝓝 p := by
  have ht : Continuous (tubeHeight M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt M e0 Y).continuousAt
  have h1 := (tube_base_height he0 hM hy htT).1
  exact (isOpen_lt continuous_const (ht.comp continuous_snd.fst)).mem_nhds
    (show 0 < tubeHeight M e0 p.2.1 by linarith)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end

