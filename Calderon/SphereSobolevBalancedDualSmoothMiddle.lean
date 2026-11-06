import Calderon.SphereSobolevBalancedDualKernelRestriction
import Calderon.SphereSobolevBalancedDualBesselPair
import Calderon.SphereSobolevBalancedDualMiddleUpper
import Calderon.SphereSobolevBalancedDualMiddleLower
import Calderon.SphereSobolevBalancedDualMiddleNorm
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL
theorem exists_contDiffOn_sphereSobolev_compatible_middle
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) (hUnique : UniqueDiffOn ℝ S)
    (Gh : X → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ))
    (Gn : X → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hGh : ContDiffOn ℝ ∞ Gh S) (hGn : ContDiffOn ℝ ∞ Gn S)
    (hCompatible : ∀ z ∈ S, ∀ u : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Gh z u) =
        Gn z (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u)) :
    ∃ G : X → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ),
      ContDiffOn ℝ ∞ G S ∧
      ∀ z ∈ S,
        (∀ u, G z (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (Gh z u)) ∧
        (∀ v, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G z v) =
          Gn z (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) ∧
        ‖G z‖ ≤ max ‖Gh z‖ ‖Gn z‖ := by
  have hE : ∀ z ∈ S,
      (((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp (Gn z),
        (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp (Gh z)) :
          SphereSobolevBalancedDualEndpointPair) ∈
        sphereSobolevBalancedDualCompatibleEndpoints :=
    fun z hz => sphereSobolevBalancedDual_besselPair_mem (Gh z) (Gn z) (hCompatible z hz)
  have hSmooth : ContDiffOn ℝ ∞ (fun z : X =>
      (((sphereSobolevBesselOrderL (-(1/2 : ℝ)) (-(3/2 : ℝ))).comp (Gn z),
        (sphereSobolevBesselOrderL (3/2 : ℝ) (1/2 : ℝ)).comp (Gh z)) :
          SphereSobolevBalancedDualEndpointPair)) S :=
    (contDiffOn_const.clm_comp hGn).prodMk (contDiffOn_const.clm_comp hGh)
  have hR := contDiffOn_sphereSobolevBalancedDualCompatibleRestriction S hUnique _ hSmooth hE
  have hMid := contDiff_sphereSobolevBalancedDualInterpolationL.comp_contDiffOn hR
  refine ⟨fun z => (sphereSobolevBesselOrderL (-(1/2 : ℝ)) (1/2 : ℝ)).comp
      (sphereSobolevBalancedDualInterpolationL
        (sphereSobolevBalancedDualCompatibleRestriction _ S hE z)),
    contDiffOn_const.clm_comp hMid,?_⟩
  intro z hz
  have hv := sphereSobolevBalancedDualCompatibleRestriction_val _ S hE z hz
  exact ⟨fun u => sphereSobolevBalancedDualMiddle_upper (Gh z) (Gn z) _ hv u,
    fun v => sphereSobolevBalancedDualMiddle_lower (Gh z) (Gn z) _ hv v,
    norm_sphereSobolevBalancedDualMiddle_le (Gh z) (Gn z) _ hv⟩

end OAI.AnisotropicCalderon.SphereHarmonic
