import Calderon.SphereSobolevMidpointFiniteCoefficients
import Calderon.FiniteHilbertBlockMidpointNorm
import Calderon.SphereSobolevOutputUpgrade
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph SpectralSylvester

lemma besselWeight_neg_two_eq_inv_square (k : ℕ) :
    besselWeight (-2 : ℝ) k = ((1 + (k : ℝ)) ^ 2)⁻¹ := by
  unfold besselWeight
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + (k : ℝ)), Real.rpow_two]

lemma sphereSobolev_balanced_endpoint_block_compatibility
    (T0 : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(3/2 : ℝ)))
    (T1 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hc : (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (i j : ℕ) (z : harmonicSphereSubspace j) :
    (T1 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i =
      (((1 + (i : ℝ)) ^ 2) / ((1 + (j : ℝ)) ^ 2)) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i := by
  have h := congrArg
    (fun F : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)) =>
      F (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) hc
  simp only [ContinuousLinearMap.comp_apply, sphereSobolevInclusionL_lp_single, map_smul] at h
  have hi := congrArg (fun u : SphereSobolev (-(3/2 : ℝ)) => u i) h
  simp only [sphereSobolevInclusionL_apply, lp.coeFn_smul, Pi.smul_apply] at hi
  norm_num only [show (-(1/2 : ℝ)) - (3/2 : ℝ) = -2 by norm_num,
    show (-(3/2 : ℝ)) - (1/2 : ℝ) = -2 by norm_num] at hi
  have hscale := congrArg (fun x : harmonicSphereSubspace i => (1 + (i : ℝ)) ^ 2 • x) hi
  simp only [besselWeight_neg_two_eq_inv_square, smul_smul,
    mul_inv_cancel₀ (by positivity : (1 + (i : ℝ)) ^ 2 ≠ 0), one_smul] at hscale
  simpa only [div_eq_mul_inv] using hscale

lemma sphereSobolev_balanced_endpoint_coefficient_finite_sum
    (T0 : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(3/2 : ℝ)))
    (u : SphereSobolev (1/2 : ℝ)) (S : Finset ℕ)
    (hu : u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k (u k))
    (i : ℕ) :
    besselWeight (-(1/2 : ℝ)) i • sphereSobolevCoefficientL (-(3/2 : ℝ)) i
      (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) =
      ∑ j ∈ S, (besselWeight 1 i / besselWeight 1 j) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j (u j))) i := by
  have hw : besselWeight (-(1/2 : ℝ)) i * besselWeight (3/2 : ℝ) i =
      besselWeight 1 i := by
    unfold besselWeight
    rw [← Real.rpow_add (by positivity : 0 < 1 + (i : ℝ))]
    norm_num
  change besselWeight (-(1/2 : ℝ)) i • (besselWeight (-(-(3/2 : ℝ))) i •
    (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) i) = _
  rw [neg_neg, smul_smul, hw]
  conv_lhs => rw [hu]
  simp only [map_sum, sphereSobolevInclusionL_lp_single, map_smul,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [show (-(1/2 : ℝ)) - (1/2 : ℝ) = -1 by norm_num]
  simp only [besselWeight, Real.rpow_one, Real.rpow_neg_one, div_eq_mul_inv]

variable
    (T0 : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(3/2 : ℝ)))
    (T1 : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hc : (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))

include hc

lemma sphereSobolev_balanced_endpoint_finite_bound
    (u : SphereSobolev (1/2 : ℝ)) (hu : u ∈ sphereSobolevFiniteSupport (1/2 : ℝ))
    (Q : Finset ℕ) :
    (∑ i ∈ Q, besselWeight (-(1/2 : ℝ)) i ^ 2 *
      ‖sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u))‖ ^ 2) ≤
      ((‖T0‖ + ‖T1‖) / 2) ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨n, hn⟩ := hu
  let S := Q ∪ Finset.range n
  have hnS : Finset.range n ⊆ S := Finset.subset_union_right
  have hQS : Q ⊆ S := Finset.subset_union_left
  have huS := sphereSobolev_eq_sum_lp_single_of_finiteSupport (1/2 : ℝ) u n hn S hnS
  have hblock : ∀ i ∈ S, ∀ j ∈ S, ∀ z : harmonicSphereSubspace j,
      (T1 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i =
        (besselWeight 1 i ^ 2 / besselWeight 1 j ^ 2) •
          (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i := by
    intro i hi j hj z
    simpa only [besselWeight, Real.rpow_one] using
      sphereSobolev_balanced_endpoint_block_compatibility T0 T1 hc i j z
  have h := finite_lp_midpoint_output_square_bound T0 T1 S (besselWeight 1)
    (fun k hk => besselWeight_pos _ _) hblock ‖T0‖ ‖T1‖
      (norm_nonneg T0) (norm_nonneg T1) le_rfl le_rfl (fun k => u k)
  have hinput : (∑ j ∈ S, ‖u j‖ ^ 2) = ‖u‖ ^ 2 := by
    have he := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) (fun k => u k) S
    rw [← huS] at he
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he.symm
  rw [hinput] at h
  have hweight (i : ℕ) : besselWeight (-(1/2 : ℝ)) i ^ 2 *
      ‖sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u))‖ ^ 2 =
      ‖besselWeight (-(1/2 : ℝ)) i • sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u))‖ ^ 2 := by
    have hNorm := norm_smul_of_nonneg (E := harmonicSphereSubspace i)
      (le_of_lt (besselWeight_pos (-(1/2 : ℝ)) i))
      (sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)))
    exact ((congrArg (fun z : ℝ => z ^ 2) hNorm).trans (mul_pow _ _ 2)).symm
  calc
    _ = ∑ i ∈ Q, ‖besselWeight (-(1/2 : ℝ)) i • sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hweight i
    _ = ∑ i ∈ Q, ‖∑ j ∈ S, (besselWeight 1 i / besselWeight 1 j) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j (u j))) i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sphereSobolev_balanced_endpoint_coefficient_finite_sum T0 u S huS i]
    _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, (besselWeight 1 i / besselWeight 1 j) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j (u j))) i‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hQS (fun i hi hni => sq_nonneg _)
    _ ≤ _ := h

lemma sphereSobolev_balanced_endpoint_cutoff_bound (u : SphereSobolev (1/2 : ℝ))
    (Q : Finset ℕ) :
    (∑ i ∈ Q, besselWeight (-(1/2 : ℝ)) i ^ 2 *
      ‖sphereSobolevCoefficientL (-(3/2 : ℝ)) i
        ((T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num))) u)‖ ^ 2) ≤
      ((‖T0‖ + ‖T1‖) / 2) ^ 2 * ‖u‖ ^ 2 := by
  apply sphereSobolev_finite_bound_of_finiteSupport (1/2 : ℝ) (-(3/2 : ℝ))
    (-(1/2 : ℝ)) ((‖T0‖ + ‖T1‖) / 2)
    (T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
  intro v hv S
  simpa only [ContinuousLinearMap.comp_apply] using
    sphereSobolev_balanced_endpoint_finite_bound T0 T1 hc v hv S

def sphereSobolevBalancedDualEndpointL :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  sphereSobolevUpgradeL (1/2 : ℝ) (-(3/2 : ℝ)) (-(1/2 : ℝ))
    ((‖T0‖ + ‖T1‖) / 2) (by positivity)
    (T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (sphereSobolev_balanced_endpoint_cutoff_bound T0 T1 hc)

lemma sphereSobolevCoefficientL_balancedDualEndpoint (u : SphereSobolev (1/2 : ℝ)) (k : ℕ) :
    sphereSobolevCoefficientL (-(1/2 : ℝ)) k (sphereSobolevBalancedDualEndpointL T0 T1 hc u) =
      sphereSobolevCoefficientL (-(3/2 : ℝ)) k
        (T0 (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) :=
  sphereSobolevCoefficientL_upgrade (1/2 : ℝ) (-(3/2 : ℝ)) (-(1/2 : ℝ))
    ((‖T0‖ + ‖T1‖) / 2) (by positivity)
    (T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (sphereSobolev_balanced_endpoint_cutoff_bound T0 T1 hc) u k

lemma norm_sphereSobolevBalancedDualEndpointL_le :
    ‖sphereSobolevBalancedDualEndpointL T0 T1 hc‖ ≤ (‖T0‖ + ‖T1‖) / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  exact norm_sphereSobolevUpgradeValue_le (1/2 : ℝ) (-(3/2 : ℝ)) (-(1/2 : ℝ))
    ((‖T0‖ + ‖T1‖) / 2) (by positivity)
    (T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (sphereSobolev_balanced_endpoint_cutoff_bound T0 T1 hc) u

lemma sphereSobolevBalancedDualEndpointL_lower_inclusion :
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevBalancedDualEndpointL T0 T1 hc) =
      T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) :=
  sphereSobolevInclusionL_upgrade (1/2 : ℝ) (-(3/2 : ℝ)) (-(1/2 : ℝ))
    ((‖T0‖ + ‖T1‖) / 2) (by norm_num) (by positivity)
    (T0.comp (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)))
    (sphereSobolev_balanced_endpoint_cutoff_bound T0 T1 hc)

lemma sphereSobolevBalancedDualEndpointL_upper_inclusion :
    (sphereSobolevBalancedDualEndpointL T0 T1 hc).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) =
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp T1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
  have hLower := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)) =>
      A (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u))
    (sphereSobolevBalancedDualEndpointL_lower_inclusion T0 T1 hc)
  have hIn := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
    (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  have hOut := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)) => A (T1 u))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num) (by norm_num))
  have hCompat := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)) => A u) hc
  simp only [ContinuousLinearMap.comp_apply] at hLower hIn hOut hCompat ⊢
  exact hLower.trans ((congrArg T0 hIn).trans (hCompat.symm.trans hOut.symm))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.besselWeight_neg_two_eq_inv_square
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_balanced_endpoint_block_compatibility
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_balanced_endpoint_coefficient_finite_sum
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_balanced_endpoint_finite_bound
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolev_balanced_endpoint_cutoff_bound
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualEndpointL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevCoefficientL_balancedDualEndpoint
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.norm_sphereSobolevBalancedDualEndpointL_le
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualEndpointL_lower_inclusion
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevBalancedDualEndpointL_upper_inclusion
