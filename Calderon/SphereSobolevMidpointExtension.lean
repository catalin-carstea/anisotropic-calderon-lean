import Calderon.SphereSobolevMidpointFiniteBound
import Calderon.SphereSobolevOutputUpgrade

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

variable
    (T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (T1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hc : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))

include hc

lemma sphereSobolev_midpoint_cutoff_bound (u : SphereSobolev 1) (S : Finset ℕ) :
    (∑ k ∈ S, besselWeight 0 k^2*‖sphereSobolevCoefficientL (-1/2:ℝ) k
      ((T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) u)‖^2) ≤
      ((‖T0‖+‖T1‖)/2)^2*‖u‖^2 := by
  apply sphereSobolev_finite_bound_of_finiteSupport 1 (-1/2:ℝ) 0 ((‖T0‖+‖T1‖)/2)
    (T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
  intro v hv Q
  simpa only [besselWeight_zero_order,one_pow,one_mul,ContinuousLinearMap.comp_apply] using
    sphereSobolev_midpoint_finite_bound T0 T1 hc ‖T0‖ ‖T1‖
      (norm_nonneg T0) (norm_nonneg T1) le_rfl le_rfl v hv Q

def sphereSobolevMidpointL : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  sphereSobolevUpgradeL 1 (-1/2:ℝ) 0 ((‖T0‖+‖T1‖)/2) (by positivity)
    (T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (sphereSobolev_midpoint_cutoff_bound T0 T1 hc)

lemma sphereSobolevCoefficientL_midpoint (u : SphereSobolev 1) (k : ℕ) :
    sphereSobolevCoefficientL 0 k (sphereSobolevMidpointL T0 T1 hc u) =
      sphereSobolevCoefficientL (-1/2:ℝ) k
        (T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) := by
  exact sphereSobolevCoefficientL_upgrade 1 (-1/2:ℝ) 0 ((‖T0‖+‖T1‖)/2) (by positivity)
    (T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (sphereSobolev_midpoint_cutoff_bound T0 T1 hc) u k

lemma norm_sphereSobolevMidpointL_le : ‖sphereSobolevMidpointL T0 T1 hc‖ ≤ (‖T0‖+‖T1‖)/2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  exact norm_sphereSobolevUpgradeValue_le 1 (-1/2:ℝ) 0 ((‖T0‖+‖T1‖)/2) (by positivity)
    (T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (sphereSobolev_midpoint_cutoff_bound T0 T1 hc) u

lemma sphereSobolevInclusionL_midpoint :
    (sphereSobolevInclusionL 0 (-1/2:ℝ) (by norm_num)).comp (sphereSobolevMidpointL T0 T1 hc) =
      T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  exact sphereSobolevInclusionL_upgrade 1 (-1/2:ℝ) 0 ((‖T0‖+‖T1‖)/2)
    (by norm_num) (by positivity)
    (T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (sphereSobolev_midpoint_cutoff_bound T0 T1 hc)

lemma sphereSobolevMidpointL_inclusion :
    (sphereSobolevMidpointL T0 T1 hc).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp T1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-1/2:ℝ) (by norm_num)
  have hlow := congrArg (fun F : SphereSobolev 1 →L[ℝ] SphereSobolev (-1/2:ℝ) =>
    F (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
      (sphereSobolevInclusionL_midpoint T0 T1 hc)
  have hin := congrArg (fun F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => F u)
    (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hout := congrArg (fun F : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) => F (T1 u))
    (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-1/2:ℝ) (by norm_num) (by norm_num))
  have hend := congrArg (fun F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) => F u) hc
  simp only [ContinuousLinearMap.comp_apply] at hlow hin hout hend ⊢
  have hinT :
      T0 (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)) =
      T0 (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) :=
    congrArg (fun v : SphereSobolev (1/2:ℝ) => T0 v) hin
  exact hlow.trans (hinT.trans (hend.symm.trans hout.symm))

end OAI.AnisotropicCalderon.SphereHarmonic
