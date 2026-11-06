import Calderon.PhysicalDegreeCasimirCompatibleNormedStructure
import Mathlib.Analysis.Calculus.ContDiff.Defs
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
/-! Comparisons within the same structure only; no alternative norm or assumed
canonical dictionary equality. -/

def physicalDegreeCasimirData_module : Module ℝ PhysicalDegreeCasimirData :=
  (inferInstance : NormedSpace ℝ PhysicalDegreeCasimirData).toModule

lemma physicalDegreeCasimirCompatibleData_normedAddCommGroup_eq_standard
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD =
      @Submodule.normedAddCommGroup ℝ PhysicalDegreeCasimirData
        (inferInstance : Ring ℝ) (inferInstance : NormedAddCommGroup PhysicalDegreeCasimirData)
        physicalDegreeCasimirData_module (physicalDegreeCasimirCompatibleData hO hD) := by
  rfl

lemma physicalDegreeCasimirCompatibleData_normedSpace_heq_standard
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    HEq (physicalDegreeCasimirCompatibleData_normedSpace hO hD)
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := PhysicalDegreeCasimirData)
        (physicalDegreeCasimirCompatibleData hO hD)) := by
  rfl

lemma contDiffOn_of_heq_codomain_structures
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {F : Type*} (G₁ G₂ : NormedAddCommGroup F)
    (V₁ : @NormedSpace 𝕜 F (inferInstance : NormedField 𝕜) G₁.toSeminormedAddCommGroup)
    (V₂ : @NormedSpace 𝕜 F (inferInstance : NormedField 𝕜) G₂.toSeminormedAddCommGroup)
    (hG : G₁ = G₂) (hV : HEq V₁ V₂) (f : X → F) (s : Set X)
    (hf : @ContDiffOn 𝕜 (inferInstance : NontriviallyNormedField 𝕜)
      X (inferInstance : NormedAddCommGroup X) (inferInstance : NormedSpace 𝕜 X)
      F G₂ V₂ ∞ f s) :
    @ContDiffOn 𝕜 (inferInstance : NontriviallyNormedField 𝕜)
      X (inferInstance : NormedAddCommGroup X) (inferInstance : NormedSpace 𝕜 X)
      F G₁ V₁ ∞ f s := by
  cases hG
  cases hV
  exact hf

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirData_module
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedAddCommGroup_eq_standard
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedSpace_heq_standard
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.contDiffOn_of_heq_codomain_structures
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
