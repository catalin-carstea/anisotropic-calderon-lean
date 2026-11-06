import Calderon.SphereSobolevMidpointFiniteCoefficients
import Calderon.FiniteHilbertBlockMidpointNorm

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph SpectralSylvester

lemma sphereSobolev_midpoint_finite_bound
    (T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (T1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hT0 : ‖T0‖ ≤ M0) (hT1 : ‖T1‖ ≤ M1)
    (u : SphereSobolev 1) (hu : u ∈ sphereSobolevFiniteSupport 1) (Q : Finset ℕ) :
    (∑ i ∈ Q, ‖sphereSobolevCoefficientL (-1/2:ℝ) i
      (T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))‖^2) ≤
      ((M0+M1)/2)^2*‖u‖^2 := by
  obtain ⟨n,hn⟩ := hu
  let S := Q ∪ Finset.range n
  have hnS : Finset.range n ⊆ S := Finset.subset_union_right
  have hQS : Q ⊆ S := Finset.subset_union_left
  have huS := sphereSobolev_eq_sum_lp_single_of_finiteSupport 1 u n hn S hnS
  have hblock : ∀ i ∈ S, ∀ j ∈ S, ∀ z : harmonicSphereSubspace j,
      (T1 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i =
        (besselWeight (1/2:ℝ) i^2/besselWeight (1/2:ℝ) j^2) •
          (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i := by
    intro i hi j hj z
    simpa only [besselWeight_half_square] using
      sphereSobolev_midpoint_block_compatibility T0 T1 hc i j z
  have h := finite_lp_midpoint_output_square_bound T0 T1 S (besselWeight (1/2:ℝ))
    (fun k hk => besselWeight_pos _ _) hblock M0 M1 hM0 hM1 hT0 hT1 (fun k => u k)
  have hinput : (∑ j ∈ S, ‖u j‖^2) = ‖u‖^2 := by
    have he := lp.norm_sum_single (p := (2:ℝ≥0∞)) (by norm_num) (fun k => u k) S
    rw [← huS] at he
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using he.symm
  rw [hinput] at h
  have hout : (∑ i ∈ S, ‖sphereSobolevCoefficientL (-1/2:ℝ) i
      (T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))‖^2) ≤
      ((M0+M1)/2)^2*‖u‖^2 := by
    simpa only [sphereSobolev_midpoint_coefficient_finite_sum T0 u S huS] using h
  apply le_trans ?_ hout
  exact Finset.sum_le_sum_of_subset_of_nonneg hQS (fun i hi hni => sq_nonneg _)

end OAI.AnisotropicCalderon.SphereHarmonic
