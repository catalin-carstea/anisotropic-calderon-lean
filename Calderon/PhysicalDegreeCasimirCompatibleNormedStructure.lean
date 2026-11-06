import Calderon.PhysicalDegreeCasimirCompatibilitySpace
import Calderon.ProdInheritedStructureData
import Calderon.PiInheritedStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic DirichletFamily.DriftBootstrap
/-! Full upfront EXPANSION-v002.json precedes source. Original eight blocks are unchanged;
two exact canonical scalar caches are additional derived instances. Explicit caches of the
original canonical inherited subtype structures, verified below by rfl evidence.
No alternative norm, module, topology, or closure premise is introduced. -/

def physicalDegreeCasimirData_smul :
    SMul ℝ PhysicalDegreeCasimirData :=
  (inferInstance : NormedSpace ℝ PhysicalDegreeCasimirData).toModule.toSMul

instance (priority := 1100) physicalDegreeCasimirData_isScalarTower :
    IsScalarTower ℝ ℝ PhysicalDegreeCasimirData :=
  IsScalarTower.left (α := PhysicalDegreeCasimirData) ℝ

instance (priority := 1100) physicalDegreeCasimirCompatibleData_normedAddCommGroup
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    NormedAddCommGroup (physicalDegreeCasimirCompatibleData hO hD) := by
  have hCanonical := Submodule.normedAddCommGroup (𝕜 := ℝ) (E := PhysicalDegreeCasimirData)
  run_tac do let out ← IO.getStdout; out.putStrLn "COMPATIBLE_CANONICAL_GROUP_CACHED"; out.flush
  try simp only [PhysicalDegreeCasimirData,
      SphereSobolevEndpointPair,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] at hCanonical
  run_tac do let out ← IO.getStdout; out.putStrLn "COMPATIBLE_CANONICAL_GROUP_NORMALIZED"; out.flush
  simpa only [id_eq, PhysicalDegreeCasimirData,
      SphereSobolevEndpointPair,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] using
    hCanonical (physicalDegreeCasimirCompatibleData hO hD)

instance (priority := 1100) physicalDegreeCasimirCompatibleData_seminormedAddCommGroup
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SeminormedAddCommGroup (physicalDegreeCasimirCompatibleData hO hD) :=
  (physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD).toSeminormedAddCommGroup

instance (priority := 1100) physicalDegreeCasimirCompatibleData_norm
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    Norm (physicalDegreeCasimirCompatibleData hO hD) :=
  (physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD).toNorm

instance (priority := 1100) physicalDegreeCasimirCompatibleData_smul
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SMul ℝ (physicalDegreeCasimirCompatibleData hO hD) :=
  Submodule.smul (S := ℝ) (R := ℝ) (M := PhysicalDegreeCasimirData)
    (physicalDegreeCasimirCompatibleData hO hD)

instance (priority := 1100) physicalDegreeCasimirCompatibleData_normedSpace
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    NormedSpace ℝ (physicalDegreeCasimirCompatibleData hO hD) := by
  have hCanonical := Submodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := PhysicalDegreeCasimirData)
  run_tac do let out ← IO.getStdout; out.putStrLn "COMPATIBLE_CANONICAL_SPACE_CACHED"; out.flush
  try simp only [PhysicalDegreeCasimirData,
      SphereSobolevEndpointPair,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] at hCanonical
  run_tac do let out ← IO.getStdout; out.putStrLn "COMPATIBLE_CANONICAL_SPACE_NORMALIZED"; out.flush
  simpa only [id_eq, physicalDegreeCasimirCompatibleData_seminormedAddCommGroup,
      physicalDegreeCasimirCompatibleData_normedAddCommGroup, PhysicalDegreeCasimirData,
      SphereSobolevEndpointPair,
      real_nontriviallyNormedField_normedField_eq,
      prod_normedAddCommGroup_seminormedAddCommGroup_eq,
      prod_seminormedAddCommGroup_addCommMonoid_eq,
      prod_normedSpace_module_eq,
      prod_seminormedAddCommGroup_topologicalSpace_eq,
      pi_normedAddCommGroup_seminormedAddCommGroup_eq,
      pi_seminormedAddCommGroup_addCommMonoid_eq,
      pi_normedSpace_module_eq,
      pi_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,
      submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,
      lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq] using
    hCanonical (physicalDegreeCasimirCompatibleData hO hD)

lemma physicalDegreeCasimirCompatibleData_norm_coe
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    ‖(x : PhysicalDegreeCasimirData)‖ = ‖x‖ := by
  rfl

lemma physicalDegreeCasimirCompatibleData_coe_add
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x y : physicalDegreeCasimirCompatibleData hO hD) :
    ((x+y : physicalDegreeCasimirCompatibleData hO hD) : PhysicalDegreeCasimirData) =
      (x : PhysicalDegreeCasimirData) + (y : PhysicalDegreeCasimirData) := by
  rfl

lemma physicalDegreeCasimirCompatibleData_coe_smul
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : ℝ) (x : physicalDegreeCasimirCompatibleData hO hD) :
    ((c • x : physicalDegreeCasimirCompatibleData hO hD) : PhysicalDegreeCasimirData) =
      @SMul.smul ℝ PhysicalDegreeCasimirData
        physicalDegreeCasimirData_smul c (x : PhysicalDegreeCasimirData) := by
  rfl

lemma physicalDegreeCasimirCompatibleData_topologicalSpace_eq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    (physicalDegreeCasimirCompatibleData_normedAddCommGroup hO hD).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (physicalDegreeCasimirCompatibleData hO hD)) := by
  rfl

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirData_smul
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirData_isScalarTower
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_smul
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedAddCommGroup
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_seminormedAddCommGroup
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_norm
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_normedSpace
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_norm_coe
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_coe_add
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_coe_smul
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_topologicalSpace_eq
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
