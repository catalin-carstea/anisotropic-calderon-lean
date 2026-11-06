import Calderon.SmoothKernelCodomainRestriction

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport
open SmoothKernelCodomainRestriction

lemma normedSpace_heq_of_group_eq_module_heq
    {F : Type*} (G₁ G₂ : NormedAddCommGroup F)
    (V₁ : @NormedSpace ℝ F (inferInstance : NormedField ℝ) G₁.toSeminormedAddCommGroup)
    (V₂ : @NormedSpace ℝ F (inferInstance : NormedField ℝ) G₂.toSeminormedAddCommGroup)
    (hG : G₁ = G₂) (hM : HEq V₁.toModule V₂.toModule) : HEq V₁ V₂ := by
  cases hG
  cases V₁
  cases V₂
  cases eq_of_heq hM
  rfl

lemma contDiffOn_of_heq_codomain_structures
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G₁ G₂ : NormedAddCommGroup F)
    (V₁ : @NormedSpace ℝ F (inferInstance : NormedField ℝ) G₁.toSeminormedAddCommGroup)
    (V₂ : @NormedSpace ℝ F (inferInstance : NormedField ℝ) G₂.toSeminormedAddCommGroup)
    (hG : G₁ = G₂) (hV : HEq V₁ V₂) (f : E → F) (s : Set E)
    (hf : @ContDiffOn ℝ (inferInstance : NontriviallyNormedField ℝ)
      E (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
      F G₂ V₂ ∞ f s) :
    @ContDiffOn ℝ (inferInstance : NontriviallyNormedField ℝ)
      E (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
      F G₁ V₁ ∞ f s := by
  cases hG
  cases hV
  exact hf

lemma contDiffOn_kernelCodomainRestriction_of_module_heq
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (C : F →L[ℝ] G)
    (GK : NormedAddCommGroup C.ker)
    (VK : @NormedSpace ℝ C.ker (inferInstance : NormedField ℝ)
      GK.toSeminormedAddCommGroup)
    (hG : GK = Submodule.normedAddCommGroup C.ker)
    (hM : HEq VK.toModule
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) C.ker).toModule)
    (f : E → F) (s : Set E) (hs : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ ∞ f s) (hz : ∀ x ∈ s, C (f x) = 0) :
    @ContDiffOn ℝ (inferInstance : NontriviallyNormedField ℝ)
      E (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
      C.ker GK VK ∞ (kernelCodomainRestriction C f s hz) s := by
  have hV : HEq VK (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) C.ker) :=
    normedSpace_heq_of_group_eq_module_heq GK
      (Submodule.normedAddCommGroup C.ker) VK
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) C.ker) hG hM
  have hCanonical :
      @ContDiffOn ℝ (inferInstance : NontriviallyNormedField ℝ)
        E (inferInstance : NormedAddCommGroup E) (inferInstance : NormedSpace ℝ E)
        C.ker (Submodule.normedAddCommGroup C.ker)
        (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) C.ker) ∞
        (kernelCodomainRestriction C f s hz) s :=
    contDiffOn_kernelCodomainRestriction C f s hs hf hz
  exact contDiffOn_of_heq_codomain_structures GK
    (Submodule.normedAddCommGroup C.ker) VK
    (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) C.ker) hG hV
    (kernelCodomainRestriction C f s hz) s hCanonical

#print axioms OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport.normedSpace_heq_of_group_eq_module_heq
#print axioms OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport.contDiffOn_of_heq_codomain_structures
#print axioms OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport.contDiffOn_kernelCodomainRestriction_of_module_heq
end OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport
