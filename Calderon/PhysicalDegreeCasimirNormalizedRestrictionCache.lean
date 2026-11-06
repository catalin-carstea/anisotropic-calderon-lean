import Calderon.PhysicalDegreeCasimirKernelStructureComparison
import Calderon.ProdInheritedStructureData
import Calderon.PiInheritedStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility DirichletFamily.DriftBootstrap
/-! Universal original-space proof caches: normalize before any actual constraint family. -/

def physicalDegreeCasimirRestrictionCoeNormalizedCache
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] := id (by
  have hValue := scalarCompatibilityRestriction_coe_of_mem
    (E := PhysicalDegreeCasimirData) (X := X) (I := I)
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_COE_GENERIC_CACHED"; out.flush
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
      clm_normedSpace_module_eq] at hValue
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_COE_GENERIC_NORMALIZED"; out.flush
  exact hValue)

def physicalDegreeCasimirRestrictionSmoothnessNormalizedCache
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] := id (by
  have hSmooth := contDiffOn_scalarCompatibilityRestriction
    (E := PhysicalDegreeCasimirData) (X := X) (I := I)
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_SMOOTH_GENERIC_CACHED"; out.flush
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
      clm_normedSpace_module_eq] at hSmooth
  run_tac do let out ← IO.getStdout; out.putStrLn "RESTRICTION_SMOOTH_GENERIC_NORMALIZED"; out.flush
  exact hSmooth)

#check @physicalDegreeCasimirRestrictionCoeNormalizedCache
#check @physicalDegreeCasimirRestrictionSmoothnessNormalizedCache
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirRestrictionCoeNormalizedCache
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirRestrictionSmoothnessNormalizedCache
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
