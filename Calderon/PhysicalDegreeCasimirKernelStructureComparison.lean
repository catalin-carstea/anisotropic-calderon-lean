import Calderon.PhysicalDegreeCasimirCanonicalStructureComparison
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility
/-! Full upfront EXPANSION-v001.json precedes source. Exact standard-KERNEL
structures, avoiding the W alias under ContDiffOn instance arguments. -/

lemma physicalDegreeCasimirCompatibleData_normedAddCommGroup_eq_kernel
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD =
      @Submodule.normedAddCommGroup ℝ PhysicalDegreeCasimirData
        (inferInstance : Ring ℝ) (inferInstance : NormedAddCommGroup PhysicalDegreeCasimirData)
        physicalDegreeCasimirData_module
        (simultaneousScalarKernel (degreeCasimirConstraintL hO hD)) := by
  rfl

lemma physicalDegreeCasimirCompatibleData_normedSpace_heq_kernel
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    HEq (physicalDegreeCasimirCompatibleData_normedSpace hO hD)
      (Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := PhysicalDegreeCasimirData)
        (simultaneousScalarKernel (degreeCasimirConstraintL hO hD))) := by
  rfl

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedAddCommGroup_eq_kernel
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedSpace_heq_kernel
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
