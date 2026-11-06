import Calderon.SphereSobolevBalancedDualEndpointStructure
import Calderon.SphereSobolevBesselOrderCompatibility
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL
lemma sphereSobolevBalancedDual_besselPair_mem
    (A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (B : SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hAB : ∀ u : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (A u) =
        B (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) :
    (((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp B,
      (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp A) :
        SphereSobolevBalancedDualEndpointPair) ∈
      sphereSobolevBalancedDualCompatibleEndpoints := by
  apply (sphereSobolevBalancedDualCompatible_mem_iff _).mpr
  apply ContinuousLinearMap.ext
  intro u
  have hBouter := DFunLike.congr_fun
    (sphereSobolevBesselOrderL_inclusion_comp (3/2 : ℝ) (-(1/2 : ℝ))
      (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (A u)
  simp only [ContinuousLinearMap.comp_apply] at hBouter
  dsimp only
  simp only [ContinuousLinearMap.comp_apply]
  rw [hBouter,hAB u]


end OAI.AnisotropicCalderon.SphereHarmonic
