import Calderon.SphereSobolevMidpointCompatibility

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma sphereSobolev_eq_sum_lp_single_of_zero (s : ℝ) (u : SphereSobolev s)
    (S : Finset ℕ) (hu : ∀ k ∉ S, u k = 0) :
    u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (u k) := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,lp.coeFn_single,Finset.sum_apply,Finset.sum_pi_single]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk,hu k hk]

lemma sphereSobolev_eq_sum_lp_single_of_finiteSupport
    (s : ℝ) (u : SphereSobolev s) (n : ℕ)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL s k u = 0)
    (S : Finset ℕ) (hS : Finset.range n ⊆ S) :
    u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (u k) := by
  apply sphereSobolev_eq_sum_lp_single_of_zero s u S
  intro k hk
  have hnk : n ≤ k := by
    by_contra hn
    exact hk (hS (Finset.mem_range.mpr (lt_of_not_ge hn)))
  rw [← sphereSobolevCoefficientL_reconstruct s k u,hu k hnk,smul_zero]

lemma besselWeight_half_square (k : ℕ) : besselWeight (1/2:ℝ) k^2 = 1+(k:ℝ) := by
  unfold besselWeight
  rw [← Real.rpow_two,← Real.rpow_mul (by positivity : 0 ≤ 1+(k:ℝ))]
  norm_num

lemma sphereSobolev_midpoint_coefficient_finite_sum
    (T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (u : SphereSobolev 1) (S : Finset ℕ)
    (hu : u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (u k))
    (i : ℕ) :
    sphereSobolevCoefficientL (-1/2:ℝ) i
      (T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) =
      ∑ j ∈ S, (besselWeight (1/2:ℝ) i/besselWeight (1/2:ℝ) j) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j (u j))) i := by
  change besselWeight (-(-1/2:ℝ)) i •
      (T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) i = _
  conv_lhs => rw [hu]
  simp only [map_sum,sphereSobolevInclusionL_lp_single,map_smul,
    lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hn : ((1/2:ℝ)-1) = -(1/2:ℝ) := by norm_num
  rw [show -(-1/2:ℝ)=(1/2:ℝ) by norm_num,hn]
  unfold besselWeight
  rw [Real.rpow_neg (by positivity : 0 ≤ 1+(j:ℝ)),div_eq_mul_inv]
  simp only [div_eq_mul_inv]

end OAI.AnisotropicCalderon.SphereHarmonic
