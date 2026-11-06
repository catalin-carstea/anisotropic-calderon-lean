import Calderon.JacobiBounds
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Set
namespace OAI.AnisotropicCalderon.JacobiIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def endpointSize (j : ℝ → E) : ℝ := max ‖j 0‖ ‖j 1‖

lemma norm_affine_endpoints_le (j : ℝ → E) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖(1-t) • j 0 + t • j 1‖ ≤ endpointSize j := by
  have h := norm_add_le ((1-t) • j 0) (t • j 1)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1] at h
  have h1 := mul_le_mul_of_nonneg_left (le_max_left ‖j 0‖ ‖j 1‖)
    (sub_nonneg.mpr ht.2)
  have h2 := mul_le_mul_of_nonneg_left (le_max_right ‖j 0‖ ‖j 1‖) ht.1
  unfold endpointSize
  nlinarith

theorem norm_solution_le (j j' f : ℝ → E) (k : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k * ‖j s‖) :
    ∀ t ∈ Icc 0 1, ‖j t‖ ≤ (8/7:ℝ) * endpointSize j := by
  have hc : ContinuousOn j (Icc (0:ℝ) 1) :=
    fun s hs => (hj s hs).continuousAt.continuousWithinAt
  obtain ⟨s,hs,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩) hc.norm
  have hforce' : ∀ u ∈ Icc 0 1, ‖f u‖ ≤ k * ‖j s‖ :=
    fun u hu => (hforce u hu).trans (mul_le_mul_of_nonneg_left (hmax hu) hk)
  have hG := norm_sub_affine_le j j' f s (k*‖j s‖) hs hj hj' hf
    (mul_nonneg hk (norm_nonneg _)) hforce'
  have hA := norm_affine_endpoints_le j s hs
  have hN : ‖j s‖ ≤ ‖j s - ((1-s) • j 0+s • j 1)‖ +
      ‖(1-s) • j 0+s • j 1‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (j s - ((1-s) • j 0+s • j 1)) ((1-s) • j 0+s • j 1)
  have hK := mul_le_mul_of_nonneg_right hk1 (norm_nonneg (j s))
  have hsBound : ‖j s‖ ≤ (8/7:ℝ)*endpointSize j := by nlinarith
  exact fun t ht => (hmax ht).trans hsBound

theorem norm_solution_le_two (j j' f : ℝ → E) (k : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k * ‖j s‖) :
    ∀ t ∈ Icc 0 1, ‖j t‖ ≤ 2 * endpointSize j := by
  have hm : 0 ≤ endpointSize j := (norm_nonneg (j 0)).trans (le_max_left _ _)
  intro t ht
  have h := norm_solution_le j j' f k hj hj' hf hk hk1 hforce t ht
  nlinarith

theorem norm_small_solution_sub_affine_le (j j' f : ℝ → E) (t k : ℝ)
    (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k * ‖j s‖) :
    ‖j t - ((1-t) • j 0+t • j 1)‖ ≤ k * endpointSize j / 4 := by
  have hm : 0 ≤ endpointSize j := (norm_nonneg (j 0)).trans (le_max_left _ _)
  have hb : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k*(2*endpointSize j) :=
    fun s hs => (hforce s hs).trans (mul_le_mul_of_nonneg_left
      (norm_solution_le_two j j' f k hj hj' hf hk hk1 hforce s hs) hk)
  have h := norm_sub_affine_le j j' f t (k*(2*endpointSize j)) ht hj hj' hf
    (by positivity) hb
  nlinarith

theorem norm_small_solution_derivative_sub_endpoints_le (j j' f : ℝ → E) (t k : ℝ)
    (ht : t ∈ Icc 0 1)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k * ‖j s‖) :
    ‖j' t - (j 1-j 0)‖ ≤ k * endpointSize j := by
  have hm : 0 ≤ endpointSize j := (norm_nonneg (j 0)).trans (le_max_left _ _)
  have hb : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k*(2*endpointSize j) :=
    fun s hs => (hforce s hs).trans (mul_le_mul_of_nonneg_left
      (norm_solution_le_two j j' f k hj hj' hf hk hk1 hforce s hs) hk)
  have h := norm_derivative_sub_endpoints_le j j' f t (k*(2*endpointSize j))
    ht hj hj' hf (by positivity) hb
  nlinarith

#print axioms norm_solution_le
#print axioms norm_small_solution_sub_affine_le
#print axioms norm_small_solution_derivative_sub_endpoints_le
end OAI.AnisotropicCalderon.JacobiIntegral
