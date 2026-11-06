import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma sphereSobolevInclusionL_lp_single (s t : ℝ) (hts : t ≤ s)
    (k : ℕ) (z : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts (lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k z) =
      besselWeight (t-s) k • lp.single (E := fun j => ↥(harmonicSphereSubspace j)) 2 k z := by
  apply lp.ext
  funext j
  rw [sphereSobolevInclusionL_apply,lp.coeFn_smul,Pi.smul_apply]
  by_cases hj : j=k
  · subst j
    rw [lp.single_apply_self]
  · rw [lp.single_apply_ne (E := fun j => ↥(harmonicSphereSubspace j)) 2 k z hj]
    simp only [smul_zero]

lemma sphereSobolev_midpoint_block_compatibility
    (T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (T1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (i j : ℕ) (z : harmonicSphereSubspace j) :
    (T1 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i =
      ((1+(i:ℝ))/(1+(j:ℝ))) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) i := by
  have h := congrArg (fun F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) =>
    F (lp.single (E := fun k => ↥(harmonicSphereSubspace k)) 2 j z)) hc
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_lp_single,map_smul] at h
  have hi := congrArg (fun u : SphereSobolev (-1/2:ℝ) => u i) h
  simp only [sphereSobolevInclusionL_apply,lp.coeFn_smul,Pi.smul_apply] at hi
  norm_num only [show (1/2:ℝ)-(3/2:ℝ) = -1 by norm_num,
    show (-1/2:ℝ)-(1/2:ℝ) = -1 by norm_num] at hi
  have hw (k : ℕ) : besselWeight (-1) k = (1+(k:ℝ))⁻¹ := by
    simp only [besselWeight,Real.rpow_neg_one]
  have hscale := congrArg (fun x : harmonicSphereSubspace i => (1+(i:ℝ)) • x) hi
  simp only [hw,smul_smul,mul_inv_cancel₀ (by positivity : (1+(i:ℝ)) ≠ 0),one_smul] at hscale
  simpa only [div_eq_mul_inv] using hscale

end OAI.AnisotropicCalderon.SphereHarmonic
