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
/-! Full upfront EXPANSION-v001.json precedes source. Additional literal actual-space
specialization only. Original zero-annihilation condition and full restricted norm remain. -/
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def physicalDegreeCasimirRestriction
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : X → PhysicalDegreeCasimirData) (s : Set X)
    (hOriginal : ∀ x ∈ s, ∀ z, degreeCasimirConstraintL hO hD z (f x) = 0) :
    X → physicalDegreeCasimirCompatibleData hO hD := by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hRestriction := scalarCompatibilityRestriction (E := PhysicalDegreeCasimirData) (X := X) (I := ConstraintIndex)
  run_tac do let out ← IO.getStdout; out.putStrLn "PHYSICAL_RESTRICTION_CACHED"; out.flush
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
      clm_normedSpace_module_eq] at hRestriction
  run_tac do let out ← IO.getStdout; out.putStrLn "PHYSICAL_RESTRICTION_NORMALIZED"; out.flush
  simpa only [id_eq, physicalDegreeCasimirCompatibleData,
      PhysicalDegreeCasimirData,
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
    hRestriction (degreeCasimirConstraintL hO hD) f s hOriginal

lemma physicalDegreeCasimirRestriction_coe_of_mem
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : X → PhysicalDegreeCasimirData) (s : Set X)
    (hOriginal : ∀ x ∈ s, ∀ z, degreeCasimirConstraintL hO hD z (f x) = 0)
    (x : X) (hx : x ∈ s) :
    (physicalDegreeCasimirRestriction hO hD f s hOriginal x : PhysicalDegreeCasimirData) = f x := by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hValue := scalarCompatibilityRestriction_coe_of_mem (E := PhysicalDegreeCasimirData) (X := X) (I := ConstraintIndex)
  run_tac do let out ← IO.getStdout; out.putStrLn "PHYSICAL_RESTRICTION_VALUE_CACHED"; out.flush
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
  run_tac do let out ← IO.getStdout; out.putStrLn "PHYSICAL_RESTRICTION_VALUE_NORMALIZED"; out.flush
  simpa only [id_eq, physicalDegreeCasimirRestriction,
      physicalDegreeCasimirCompatibleData,
      PhysicalDegreeCasimirData,
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
    hValue (degreeCasimirConstraintL hO hD) f s hOriginal x hx


#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirRestriction
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirRestriction_coe_of_mem
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
