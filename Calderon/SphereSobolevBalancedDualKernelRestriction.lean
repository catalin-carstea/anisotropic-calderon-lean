import Calderon.SphereSobolevBalancedDualEndpointStructure
import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.SmoothKernelCodomainStructureTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
open OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevBesselOrderL

-- The original compatible kernel and its canonical structures are retained.

/-- Restriction of a pair family to the compatible kernel, with codomain the original
kernel submodule itself (no codomain retyping). -/
def sphereSobolevBalancedDualCompatibleRestriction
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (E : X → SphereSobolevBalancedDualEndpointPair) (S : Set X)
    (hE : ∀ z ∈ S, E z ∈ sphereSobolevBalancedDualCompatibleEndpoints) :
    X → sphereSobolevBalancedDualCompatibleEndpoints := by
  classical
  exact fun z => if hz : z ∈ S then ⟨E z,hE z hz⟩ else 0

lemma sphereSobolevBalancedDualCompatibleRestriction_val
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (E : X → SphereSobolevBalancedDualEndpointPair) (S : Set X)
    (hE : ∀ z ∈ S, E z ∈ sphereSobolevBalancedDualCompatibleEndpoints)
    (z : X) (hz : z ∈ S) :
    (sphereSobolevBalancedDualCompatibleRestriction E S hE z).val = E z := by
  simp only [sphereSobolevBalancedDualCompatibleRestriction,dif_pos hz]

lemma contDiffOn_sphereSobolevBalancedDualCompatibleRestriction
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) (hUnique : UniqueDiffOn ℝ S)
    (E : X → SphereSobolevBalancedDualEndpointPair) (hSmooth : ContDiffOn ℝ ∞ E S)
    (hE : ∀ z ∈ S, E z ∈ sphereSobolevBalancedDualCompatibleEndpoints) :
    ContDiffOn ℝ ∞ (sphereSobolevBalancedDualCompatibleRestriction E S hE) S := by
  have hg := contDiffOn_kernelCodomainRestriction (E := X)
    (F := SphereSobolevBalancedDualEndpointPair)
    (G := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(3/2 : ℝ)))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    sphereSobolevBalancedDualCompatibleNormedSpace_module_eq] at hg
  exact hg sphereSobolevBalancedDualEndpointDefectL E S hUnique hSmooth
    (fun z hz => hE z hz)

end OAI.AnisotropicCalderon.SphereHarmonic
