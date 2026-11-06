import Calderon.PhysicalDegreeCasimirKernelStructureComparison
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility
/-! Fix the original structures before any concrete restriction/function/s/zero
proof; no norm or topology replacement. -/

def physicalDegreeCasimirKernelSmoothnessTransportCache
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) := id (by
  have hG := physicalDegreeCasimirCompatibleData_normedAddCommGroup_eq_kernel hO hD
  have hV := physicalDegreeCasimirCompatibleData_normedSpace_heq_kernel hO hD
  run_tac do let out ← IO.getStdout; out.putStrLn "KERNEL_TRANSPORT_EQUALITIES_READY"; out.flush
  have hTransfer := contDiffOn_of_heq_codomain_structures
    (𝕜 := ℝ) (X := X) _ _ _ _ hG hV
  run_tac do let out ← IO.getStdout; out.putStrLn "KERNEL_TRANSPORT_UNIVERSAL_READY"; out.flush
  exact hTransfer)

#check @physicalDegreeCasimirKernelSmoothnessTransportCache
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirKernelSmoothnessTransportCache
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
