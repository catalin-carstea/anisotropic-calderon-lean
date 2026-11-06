import Calderon.PhysicalDegreeCasimirCompatibleNormedStructure
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic
/-! Two actual canonical projection equalities. -/

lemma physicalDegreeCasimirCompatibleData_addCommMonoid_eq_standard
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    (physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD).toSeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid =
      (physicalDegreeCasimirCompatibleData hO hD).addCommMonoid := by
  rfl

lemma physicalDegreeCasimirCompatibleData_module_eq_standard
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    (physicalDegreeCasimirCompatibleData_normedSpace hO hD).toModule =
      (physicalDegreeCasimirCompatibleData hO hD).module := by
  rfl

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_addCommMonoid_eq_standard
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_module_eq_standard
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
