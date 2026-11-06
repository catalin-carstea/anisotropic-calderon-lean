import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon

lemma norm_firstOrder_remainder_le_of_fderiv_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (hs : Convex ℝ s) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ p ∈ s, DifferentiableAt ℝ f p)
    (hLip : ∀ p ∈ s, ∀ q ∈ s,
      ‖fderiv ℝ f p - fderiv ℝ f q‖ ≤ L * ‖p-q‖)
    (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ L * ‖y-x‖ ^ 2 := by
  have hBound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ L * ‖y-x‖ := by
    intro z hz
    exact (hLip z (hs.segment_subset hx hy hz) x hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL)
  have hRem := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z (hs.segment_subset hx hy hz)) hBound
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using hRem

lemma norm_Lp_two_row_remainder_le
    {α E : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Lp ℝ 2 μ) (f : E → α → ℝ)
    (s : Set E) (hs : Convex ℝ s) (L : ℝ) (hL : 0 ≤ L)
    (hFields : ∀ᵐ z ∂μ,
      (∀ p ∈ s, DifferentiableAt ℝ (fun q => f q z) p) ∧
      (∀ p ∈ s, ∀ q ∈ s,
        ‖fderiv ℝ (fun r => f r z) p - fderiv ℝ (fun r => f r z) q‖ ≤ L * ‖p-q‖))
    (x y : E) (hx : x ∈ s) (hy : y ∈ s)
    (hX : (F x : α → ℝ) =ᵐ[μ] f x) (hY : (F y : α → ℝ) =ᵐ[μ] f y)
    (D : Lp ℝ 2 μ)
    (hD : (D : α → ℝ) =ᵐ[μ]
      (fun z => fderiv ℝ (fun r => f r z) x (y-x))) :
    ‖F y - F x - D‖ ≤
      measureUnivNNReal μ ^ (2 : ENNReal).toReal⁻¹ * (L * ‖y-x‖ ^ 2) := by
  apply Lp.norm_le_of_ae_bound (mul_nonneg hL (sq_nonneg _))
  filter_upwards [Lp.coeFn_sub (F y - F x) D,
    Lp.coeFn_sub (F y) (F x), hX, hY, hD, hFields] with z hSub hRows hXz hYz hDz hFz
  change (F y - F x - D) z = (F y - F x) z - D z at hSub
  change (F y - F x) z = F y z - F x z at hRows
  rw [hSub, hRows, hXz, hYz, hDz]
  exact norm_firstOrder_remainder_le_of_fderiv_lipschitz
    (fun r => f r z) s hs L hL hFz.1 hFz.2 x y hx hy

end OAI.AnisotropicCalderon
#print axioms OAI.AnisotropicCalderon.norm_firstOrder_remainder_le_of_fderiv_lipschitz
#print axioms OAI.AnisotropicCalderon.norm_Lp_two_row_remainder_le
