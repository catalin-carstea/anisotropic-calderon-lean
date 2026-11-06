import Calderon.SphereSobolevCompletion
import Mathlib.Analysis.Normed.Lp.lpHolder

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

lemma besselWeight_sub_le_one (s t : ℝ) (hts : t ≤ s) (k : ℕ) :
    besselWeight (t-s) k ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by have h : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith : (1:ℝ) ≤ 1+(k:ℝ))
    (sub_nonpos.mpr hts)

def sphereSobolevInclusionL (s t : ℝ) (hts : t ≤ s) :
    SphereSobolev s →L[ℝ] SphereSobolev t :=
  lp.mapCLM 2
    (fun k : ℕ => besselWeight (t-s) k • ContinuousLinearMap.id ℝ (harmonicSphereSubspace k))
    (show (0:ℝ) ≤ 1 by norm_num) (by
      intro k
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro x
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,norm_smul,
        Real.norm_eq_abs,abs_of_pos (besselWeight_pos (t-s) k),one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (besselWeight_sub_le_one s t hts k))

lemma sphereSobolevInclusionL_apply (s t : ℝ) (hts : t ≤ s)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevInclusionL s t hts u k = besselWeight (t-s) k • u k := rfl

lemma norm_sphereSobolevInclusionL_le (s t : ℝ) (hts : t ≤ s) :
    ‖sphereSobolevInclusionL s t hts‖ ≤ 1 := by
  unfold sphereSobolevInclusionL
  exact lp.norm_mapCLM_le _ _ _ _

lemma sphereSobolevCoefficientL_inclusion (s t : ℝ) (hts : t ≤ s)
    (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevCoefficientL t k (sphereSobolevInclusionL s t hts u) =
      sphereSobolevCoefficientL s k u := by
  change besselWeight (-t) k • (besselWeight (t-s) k • u k) = besselWeight (-s) k • u k
  rw [smul_smul]
  congr 1
  unfold besselWeight
  rw [← Real.rpow_add (by positivity : 0 < 1+(k:ℝ))]
  congr 1
  ring

lemma sphereSobolevInclusionL_single (s t : ℝ) (hts : t ≤ s)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a) = sphereSobolevSingleL t k a := by
  apply sphereSobolev_ext t
  intro j
  rw [sphereSobolevCoefficientL_inclusion]
  by_cases hj : j=k
  · subst j
    rw [sphereSobolevCoefficientL_single_self,sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne s k j hj,sphereSobolevCoefficientL_single_ne t k j hj]

lemma sphereSobolevInclusionL_injective (s t : ℝ) (hts : t ≤ s) :
    Function.Injective (sphereSobolevInclusionL s t hts) := by
  intro u v huv
  apply sphereSobolev_ext s
  intro k
  have h := congrArg (sphereSobolevCoefficientL t k) huv
  simpa only [sphereSobolevCoefficientL_inclusion] using h

lemma sphereSobolevInclusionL_refl (s : ℝ) :
    sphereSobolevInclusionL s s (le_refl s) = ContinuousLinearMap.id ℝ (SphereSobolev s) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext s
  intro k
  exact sphereSobolevCoefficientL_inclusion s s (le_refl s) u k

lemma sphereSobolevInclusionL_trans (s t r : ℝ) (hts : t ≤ s) (hrt : r ≤ t) :
    (sphereSobolevInclusionL t r hrt).comp (sphereSobolevInclusionL s t hts) =
      sphereSobolevInclusionL s r (le_trans hrt hts) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext r
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion]

lemma denseRange_sphereSobolevInclusionL (s t : ℝ) (hts : t ≤ s) :
    DenseRange (sphereSobolevInclusionL s t hts) := by
  intro u
  have hmem (n : ℕ) : sphereSobolevPartialSum t n u ∈ Set.range (sphereSobolevInclusionL s t hts) := by
    refine ⟨∑ k ∈ Finset.range n, sphereSobolevSingleL s k (sphereSobolevCoefficientL t k u), ?_⟩
    simp only [map_sum,sphereSobolevInclusionL_single,sphereSobolevPartialSum]
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum t u)
    (Eventually.of_forall fun n => subset_closure (hmem n))

end OAI.AnisotropicCalderon.SphereHarmonic
