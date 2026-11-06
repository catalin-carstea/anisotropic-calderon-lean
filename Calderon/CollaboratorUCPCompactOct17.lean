import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Metric
namespace OAI.AnisotropicCalderon

/-- A continuous function positive on a compact set has a positive lower bound there. -/
theorem exists_pos_lower_of_compact {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : ContinuousOn f S) (hpos : ∀ p ∈ S, 0 < f p) :
    ∃ α > 0, ∀ p ∈ S, α ≤ f p := by
  rcases S.eq_empty_or_nonempty with h | hne
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn hne hf
    exact ⟨f p0, hpos p0 hp0, fun p hp => hmin hp⟩

/-- Upper bound for a continuous function on a compact set. -/
theorem exists_upper_of_compact {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : ContinuousOn f S) : ∃ C, ∀ p ∈ S, |f p| ≤ C := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  exact ⟨C, fun p hp => by simpa [Real.norm_eq_abs] using hC p hp⟩

/-- Helper: a two-homogeneous function vanishes at zero. -/
theorem quad_zero (G : R3 → (Fin 3 → ℝ) → ℝ)
    (hhom : ∀ x (t : ℝ) ξ, G x (t • ξ) = t ^ 2 * G x ξ) (x : R3) : G x 0 = 0 := by
  have := hhom x 0 0
  simpa using this

/-- Helper: decomposition along the unit sphere. -/
theorem quad_unit (G : R3 → (Fin 3 → ℝ) → ℝ)
    (hhom : ∀ x (t : ℝ) ξ, G x (t • ξ) = t ^ 2 * G x ξ) (x : R3) {ξ : Fin 3 → ℝ}
    (hξ : ξ ≠ 0) :
    ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin 3 → ℝ) 1 ∧ G x ξ = ‖ξ‖ ^ 2 * G x (‖ξ‖⁻¹ • ξ) := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  refine ⟨?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · rw [← hhom, smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- Two-homogeneous continuous families are bounded by `C ‖ξ‖²` over a compact set
(`ξ : Fin 3 → ℝ` with its sup norm). -/
theorem quad_upper {K : Set R3} (hK : IsCompact K) (G : R3 → (Fin 3 → ℝ) → ℝ)
    (hG : Continuous (fun p : R3 × (Fin 3 → ℝ) => G p.1 p.2))
    (hhom : ∀ x (t : ℝ) ξ, G x (t • ξ) = t ^ 2 * G x ξ) :
    ∃ C, ∀ x ∈ K, ∀ ξ, |G x ξ| ≤ C * ‖ξ‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_upper_of_compact (hK.prod (isCompact_sphere (0 : Fin 3 → ℝ) 1))
    hG.continuousOn
  refine ⟨C, fun x hx ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ; simp [quad_zero G hhom x]
  · obtain ⟨hu, hEq⟩ := quad_unit G hhom x hξ
    have h1 := hC (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hu⟩
    rw [hEq, abs_mul, abs_of_nonneg (by positivity), mul_comm C]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- ... and bounded below by `α ‖ξ‖²` if positive for `ξ ≠ 0`. -/
theorem quad_lower {K : Set R3} (hK : IsCompact K) (G : R3 → (Fin 3 → ℝ) → ℝ)
    (hG : Continuous (fun p : R3 × (Fin 3 → ℝ) => G p.1 p.2))
    (hhom : ∀ x (t : ℝ) ξ, G x (t • ξ) = t ^ 2 * G x ξ)
    (hpos : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → 0 < G x ξ) :
    ∃ α > 0, ∀ x ∈ K, ∀ ξ, α * ‖ξ‖ ^ 2 ≤ G x ξ := by
  obtain ⟨α, hα, hαS⟩ := exists_pos_lower_of_compact
    (hK.prod (isCompact_sphere (0 : Fin 3 → ℝ) 1)) hG.continuousOn (by
      rintro ⟨x, u⟩ ⟨hx, hu⟩
      refine hpos x hx u ?_
      rintro rfl
      simp at hu)
  refine ⟨α, hα, fun x hx ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ; simp [quad_zero G hhom x]
  · obtain ⟨hu, hEq⟩ := quad_unit G hhom x hξ
    have h1 := hαS (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hu⟩
    rw [hEq, mul_comm α]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

end OAI.AnisotropicCalderon
