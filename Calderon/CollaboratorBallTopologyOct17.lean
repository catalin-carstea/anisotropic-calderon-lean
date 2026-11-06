import Calderon.SmoothSobolevBridge
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.PathConnected

/-! Connectedness of a ball with two small closed balls removed (helper for tasks 07–09). -/

open Metric Set
namespace OAI.AnisotropicCalderon

theorem exists_perp_ne_zero (v : R3) : ∃ n : R3, n ≠ 0 ∧ inner ℝ n v = 0 := by
  set K : Submodule ℝ R3 := ℝ ∙ v
  have h1 := K.finrank_add_finrank_orthogonal
  have h2 : Module.finrank ℝ K ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({v} : Set R3)
  have h3 : Module.finrank ℝ R3 = 3 := by simp
  have h4 : Kᗮ ≠ ⊥ := by
    intro h; rw [h] at h1; simp at h1; omega
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨n, hn0, ?_⟩
  have := (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).1 hn
  rw [real_inner_comm]; exact this

theorem isPathConnected_shell {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsPathConnected {x : R3 | r < ‖x‖ ∧ ‖x‖ < R} := by
  have hrank : 1 < Module.rank ℝ R3 := by
    rw [← Module.finrank_eq_rank]; simp
  have hS := isPathConnected_sphere hrank (0 : R3) zero_le_one
  have hI : IsPathConnected (Ioo r R) := (convex_Ioo r R).isPathConnected (nonempty_Ioo.2 hrR)
  have := (hS.prod hI).image (f := fun z : R3 × ℝ => z.2 • z.1) (by fun_prop)
  convert this using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_prod, mem_sphere_iff_norm, sub_zero, mem_Ioo,
    Prod.exists]
  constructor
  · rintro ⟨h1, h2⟩
    have hx : ‖x‖ ≠ 0 := by linarith
    refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, h1, h2⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx]
    · rw [smul_smul, mul_inv_cancel₀ hx, one_smul]
  · rintro ⟨ω, t, ⟨hω, h1, h2⟩, rfl⟩
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact ⟨h1, h2⟩


/-- Moving from `x` in direction `n` with `⟪n, x - p⟫ ≥ 0` does not decrease the distance to `p`. -/
theorem norm_add_smul_sub_ge {x p n : R3} (h : 0 ≤ inner ℝ n (x - p)) {s : ℝ} (hs : 0 ≤ s) :
    ‖x - p‖ ≤ ‖x + s • n - p‖ := by
  have e : x + s • n - p = (x - p) + s • n := by abel
  rw [e]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm]
  nlinarith [sq_nonneg ‖s • n‖]

/-- Removing two (possibly equal or overlapping) closed balls lying inside the open ball
`ball 0 R` of `R3` leaves a connected set. -/
theorem isConnected_ball_diff_two {R ρ : ℝ} {p q : R3} (hρ : 0 < ρ)
    (hp : closedBall p ρ ⊆ ball 0 R) (hq : closedBall q ρ ⊆ ball 0 R) :
    IsConnected (ball (0 : R3) R \ (closedBall p ρ ∪ closedBall q ρ)) := by
  set K := closedBall p ρ ∪ closedBall q ρ
  set S := ball (0 : R3) R \ K
  have hKc : IsCompact K := (isCompact_closedBall p ρ).union (isCompact_closedBall q ρ)
  have hKne : K.Nonempty := ⟨p, Or.inl (mem_closedBall_self hρ.le)⟩
  obtain ⟨k, hk, hkmax⟩ := hKc.exists_isMaxOn hKne continuous_norm.continuousOn
  have hKR : K ⊆ ball 0 R := union_subset hp hq
  have hkR : ‖k‖ < R := by simpa using hKR hk
  set r := (‖k‖ + R) / 2
  set c := (r + R) / 2
  have hr0 : 0 ≤ r := by simp only [r]; linarith [norm_nonneg k]
  have hrR : r < R := by simp only [r]; linarith
  set T := {x : R3 | r < ‖x‖ ∧ ‖x‖ < R}
  have hTS : T ⊆ S := by
    rintro x ⟨h1, h2⟩
    refine ⟨by simpa using h2, fun hxK => ?_⟩
    have : ‖x‖ ≤ ‖k‖ := hkmax hxK
    simp only [r] at h1; linarith
  have hT := isPathConnected_shell hr0 hrR
  -- every point of `S` joins `T`
  have key : ∀ x ∈ S, ∃ z ∈ T, JoinedIn S x z := by
    intro x hx
    by_cases hxc : c < ‖x‖
    · refine ⟨x, ⟨by simp only [c] at hxc; linarith, by simpa using hx.1⟩, JoinedIn.refl hx⟩
    push Not at hxc
    obtain ⟨m, hm0, hm⟩ := exists_perp_ne_zero (q - p)
    obtain ⟨n, hn0, hnqp, hnx⟩ : ∃ n : R3, n ≠ 0 ∧ inner ℝ n (q - p) = 0 ∧
        0 ≤ inner ℝ n (x - p) := by
      rcases le_total 0 (inner ℝ m (x - p)) with h | h
      · exact ⟨m, hm0, hm, h⟩
      · exact ⟨-m, neg_ne_zero.2 hm0, by simp [hm], by simpa using h⟩
    have hnx' : 0 ≤ inner ℝ n (x - q) := by
      have : x - q = (x - p) - (q - p) := by abel
      rw [this, inner_sub_right, hnqp, sub_zero]; exact hnx
    have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
    set f : ℝ → ℝ := fun t => ‖x + t • n‖
    have hf : Continuous f := by fun_prop
    set t₁ := (c + ‖x‖) / ‖n‖
    have ht₁ : 0 ≤ t₁ := div_nonneg (by simp only [c]; linarith [norm_nonneg x]) hnpos.le
    have hft₁ : c ≤ f t₁ := by
      have h1 : ‖t₁ • n‖ = c + ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₁, div_mul_cancel₀ _ hnpos.ne']
      have h2 := norm_sub_norm_le (t₁ • n) (-x)
      rw [norm_neg, sub_neg_eq_add, add_comm] at h2
      simp only [f]; linarith
    have hf0 : f 0 ≤ c := by simpa [f] using hxc
    obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_Icc ht₁ hf.continuousOn ⟨hf0, hft₁⟩
    refine ⟨x + t₀ • n, ⟨?_, ?_⟩, JoinedIn.of_segment_subset ?_⟩
    · rw [show ‖x + t₀ • n‖ = f t₀ from rfl, hft₀]; simp only [c]; linarith
    · rw [show ‖x + t₀ • n‖ = f t₀ from rfl, hft₀]; simp only [c]; linarith
    · rw [segment_eq_image']
      rintro _ ⟨θ, hθ, rfl⟩
      show x + θ • (x + t₀ • n - x) ∈ S
      have e : x + θ • (x + t₀ • n - x) = x + (θ * t₀) • n := by
        rw [add_sub_cancel_left, smul_smul]
      rw [e]
      have hs : 0 ≤ θ * t₀ := mul_nonneg hθ.1 ht₀.1
      refine ⟨?_, ?_⟩
      · have hxb : x ∈ ball (0 : R3) R := hx.1
        have hyb : x + t₀ • n ∈ ball (0 : R3) R := by
          rw [mem_ball_zero_iff, show ‖x + t₀ • n‖ = f t₀ from rfl, hft₀]
          simp only [c]; linarith
        have := (convex_ball (0 : R3) R).add_smul_sub_mem hxb hyb hθ
        rwa [add_sub_cancel_left, smul_smul] at this
      · rintro (h | h)
        · apply hx.2 (Or.inl _)
          rw [mem_closedBall, dist_eq_norm] at h ⊢
          exact (norm_add_smul_sub_ge hnx hs).trans h
        · apply hx.2 (Or.inr _)
          rw [mem_closedBall, dist_eq_norm] at h ⊢
          exact (norm_add_smul_sub_ge hnx' hs).trans h
  obtain ⟨z₀, hz₀, -⟩ := id hT
  have hPC : IsPathConnected S := by
    refine ⟨z₀, hTS hz₀, fun y hy => ?_⟩
    obtain ⟨z, hz, hyz⟩ := key y hy
    exact ((hT.joinedIn z₀ hz₀ z hz).mono hTS).trans hyz.symm
  exact hPC.isConnected

theorem isConnected_ball_diff_one {R ρ : ℝ} {p : R3} (hρ : 0 < ρ)
    (hp : closedBall p ρ ⊆ ball 0 R) : IsConnected (ball (0 : R3) R \ closedBall p ρ) := by
  simpa using isConnected_ball_diff_two hρ hp hp

end OAI.AnisotropicCalderon
