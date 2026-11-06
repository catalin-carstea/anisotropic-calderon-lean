import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem norm_iteratedFDeriv_clm_apply_le_uniform
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : X → (Y →L[ℝ] Z)) (g : X → Y) (E : X → Z)
    (U A : Set X) (N : ℕ) (C : ℝ)
    (hU : IsOpen U) (hAU : A ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hE : ∀ x ∈ U, E x = f x (g x))
    (_hC : 0 ≤ C)
    (hBound : ∀ i : ℕ, i ≤ N → ∀ x ∈ A,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C) :
    ∀ n : ℕ, n ≤ N → ∀ x ∈ A,
      ‖iteratedFDeriv ℝ n E x‖ ≤
        C * ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  intro n hn x hxA
  have hxU : x ∈ U := hAU hxA
  have hLocal : E =ᶠ[𝓝 x] (fun y => f y (g y)) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hE y hy
  have hDerivative : iteratedFDeriv ℝ n E x =
      iteratedFDeriv ℝ n (fun y => f y (g y)) x :=
    (hLocal.iteratedFDeriv ℝ n).eq_of_nhds
  have hFWithin (i : ℕ) :
      iteratedFDerivWithin ℝ i f U x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_of_isOpen i hU hxU
  have hGWithin (i : ℕ) :
      iteratedFDerivWithin ℝ i g U x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_of_isOpen i hU hxU
  have hApplyWithin :
      iteratedFDerivWithin ℝ n (fun y => f y (g y)) U x =
        iteratedFDeriv ℝ n (fun y => f y (g y)) x :=
    iteratedFDerivWithin_of_isOpen n hU hxU
  have hLe := norm_iteratedFDerivWithin_clm_apply hf hg hU.uniqueDiffOn hxU
    (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [hApplyWithin] at hLe
  simp_rw [hFWithin, hGWithin] at hLe
  calc
    ‖iteratedFDeriv ℝ n E x‖ =
        ‖iteratedFDeriv ℝ n (fun y => f y (g y)) x‖ := congrArg norm hDerivative
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ := hLe
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        C * ((Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hn
      calc
        _ ≤ (Nat.choose n i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hBound i hiN x hxA) (Nat.cast_nonneg _))
            (norm_nonneg _)
        _ = _ := by ac_rfl
    _ = C * ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
      rw [Finset.mul_sum]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
