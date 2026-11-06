import Calderon.JacobiEndpoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

open Set MeasureTheory
namespace OAI.AnisotropicCalderon.JacobiIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "⟪" x "," y "⟫" => inner ℝ x y

noncomputable def indexIntegral (j j' f : ℝ → E) : ℝ :=
  ∫ s in (0:ℝ)..1, ‖j' s‖^2+⟪f s,j s⟫

theorem indexIntegral_eq_endpoints (j j' f : ℝ → E)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) :
    indexIntegral j j' f = ⟪j' 1,j 1⟫-⟪j' 0,j 0⟫ := by
  have hc : ContinuousOn j (Icc 0 1) :=
    fun s hs => (hj s hs).continuousAt.continuousWithinAt
  have hc' : ContinuousOn j' (Icc 0 1) :=
    fun s hs => (hj' s hs).continuousAt.continuousWithinAt
  have hF : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u => ⟪j' u,j u⟫)
      (‖j' s‖^2+⟪f s,j s⟫) s := by
    intro s hs
    have hs' : s ∈ Icc (0:ℝ) 1 := by simpa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
    simpa only [real_inner_self_eq_norm_sq] using (hj' s hs').inner ℝ (hj s hs')
  have hint : IntervalIntegrable (fun s => ‖j' s‖^2+⟪f s,j s⟫) volume 0 1 :=
    ((hc'.norm.pow 2).add (hf.inner hc)).intervalIntegrable_of_Icc (by norm_num)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint

theorem abs_indexIntegral_sub_norm_sq_le (j j' f : ℝ → E) (k : ℝ)
    (hj : ∀ s ∈ Icc 0 1, HasDerivAt j (j' s) s)
    (hj' : ∀ s ∈ Icc 0 1, HasDerivAt j' (f s) s)
    (hf : ContinuousOn f (Icc 0 1)) (hk : 0 ≤ k) (hk1 : k ≤ 1)
    (hforce : ∀ s ∈ Icc 0 1, ‖f s‖ ≤ k*‖j s‖) :
    |indexIntegral j j' f-‖j 1-j 0‖^2| ≤ 2*k*(endpointSize j)^2 := by
  rw [indexIntegral_eq_endpoints j j' f hj hj' hf]
  exact abs_endpoint_pair_sub_norm_sq_le j j' f k hj hj' hf hk hk1 hforce

#print axioms indexIntegral_eq_endpoints
#print axioms abs_indexIntegral_sub_norm_sq_le
end OAI.AnisotropicCalderon.JacobiIntegral
