import Calderon.PhysicalDegreeCasimirSmoothRestrictionCore
import Calderon.PhysicalDegreeCasimirScalarRestrictionSpecialization
import Calderon.PhysicalDegreeCasimirCompatibilitySpace
import Calderon.ClosedScalarCompatibilityQuotient
import Calderon.ProdInheritedStructureData
import Calderon.PiInheritedStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
import Calderon.PhysicalDegreeCasimirCompatibleNormedStructure
import Calderon.PhysicalDegreeCasimirCanonicalStructureComparison
import Calderon.PhysicalDegreeCasimirKernelStructureComparison
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility DirichletFamily.DriftBootstrap
/-! Literal actual-space specialization only. The original zero-annihilation condition
and full restricted norm remain. -/
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma contDiffOn_physicalDegreeCasimirRestriction
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : X → PhysicalDegreeCasimirData) (s : Set X) (hs : IsOpen s)
    (hOriginal : ∀ x ∈ s, ∀ z, degreeCasimirConstraintL hO hD z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (physicalDegreeCasimirRestriction hO hD f s hOriginal) s := by
  have hActual := physicalDegreeCasimirScalarRestrictionSmoothness hO hD f s hs hOriginal hf
  have hValue := physicalDegreeCasimirScalarRestrictionCoeCache (X := X) hO hD
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_ACTUAL_SPECIALIZATION_READY"; out.flush
  apply hActual.congr
  intro x hx
  apply Subtype.ext
  have hStandardValue := hValue f s hOriginal x hx
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_ACTUAL_POINT_READY"; out.flush
  exact (physicalDegreeCasimirRestriction_coe_of_mem hO hD f s hOriginal x hx).trans hStandardValue.symm

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.contDiffOn_physicalDegreeCasimirRestriction
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
