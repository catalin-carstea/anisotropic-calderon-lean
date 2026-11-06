import Calderon.PhysicalDegreeFiniteCasimirScalar
import Calderon.ClosedScalarCompatibilityQuotient
import Calderon.ProdInheritedStructureData
import Calderon.PiInheritedStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility DirichletFamily.DriftBootstrap

def degreeCasimirConstraintL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1))) →
      PhysicalDegreeCasimirData →L[ℝ] ℝ
  | Sum.inl z => degreeEndpointScalarL z.1 z.2.1 z.2.2
  | Sum.inr (Sum.inl z) => degreeFiniteCasimirScalarL hO hD z.1.1 z.1.2 z.2.1 z.2.2
  | Sum.inr (Sum.inr z) => degreeAdjointScalarL hO hD z.1 z.2.1 z.2.2

def physicalDegreeCasimirCompatibleData
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    Submodule ℝ PhysicalDegreeCasimirData := by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hKernel := simultaneousScalarKernel (E := PhysicalDegreeCasimirData) (I := ConstraintIndex)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_KERNEL_CACHED"
    out.flush
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
      clm_normedSpace_module_eq] at hKernel
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_KERNEL_NORMALIZED"
    out.flush
  simpa only [PhysicalDegreeCasimirData,
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
      clm_normedSpace_module_eq] using hKernel (degreeCasimirConstraintL hO hD)

lemma mem_physicalDegreeCasimirCompatibleData_iff
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (x : PhysicalDegreeCasimirData) :
    x ∈ physicalDegreeCasimirCompatibleData hO hD ↔
      ∀ z, degreeCasimirConstraintL hO hD z x = 0 := by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hMem := mem_simultaneousScalarKernel_iff (E := PhysicalDegreeCasimirData) (I := ConstraintIndex)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_MEM_CACHED"
    out.flush
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
      clm_normedSpace_module_eq] at hMem
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_MEM_NORMALIZED"
    out.flush
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
      clm_normedSpace_module_eq] using hMem (degreeCasimirConstraintL hO hD) x

lemma isClosed_physicalDegreeCasimirCompatibleData
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    IsClosed (physicalDegreeCasimirCompatibleData hO hD : Set PhysicalDegreeCasimirData) := by
  have hTopology :
      (inferInstance : NormedAddCommGroup PhysicalDegreeCasimirData).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace PhysicalDegreeCasimirData) := by
    rfl
  run_tac do let out ← IO.getStdout; out.putStrLn "DEGREE_CLOSED_TOPOLOGY_READY"; out.flush
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hClosed := isClosed_simultaneousScalarKernel (E := PhysicalDegreeCasimirData) (I := ConstraintIndex)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_CLOSED_CACHED"
    out.flush
  try simp only [hTopology, PhysicalDegreeCasimirData,
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
      clm_normedSpace_module_eq] at hClosed
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DEGREE_CLOSED_NORMALIZED"
    out.flush
  simpa only [id_eq, hTopology, physicalDegreeCasimirCompatibleData,
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
      clm_normedSpace_module_eq] using hClosed (degreeCasimirConstraintL hO hD)

instance physicalDegreeCasimirCompatibleData_isClosed
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    IsClosed (physicalDegreeCasimirCompatibleData hO hD : Set PhysicalDegreeCasimirData) :=
  isClosed_physicalDegreeCasimirCompatibleData hO hD

lemma physicalDegreeCasimirCompatibleData_endpoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (m : ℕ) (u : SphereSobolev (3/2:ℝ)) (v : harmonicSphereSubspace m) :
    degreeEndpointScalarL m u v x.1 = 0 :=
  (mem_physicalDegreeCasimirCompatibleData_iff hO hD x.1).1 x.2 (Sum.inl ⟨m,u,v⟩)

lemma physicalDegreeCasimirCompatibleData_casimir
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    degreeFiniteCasimirScalarL hO hD ncut mcut u v x.1 = 0 :=
  (mem_physicalDegreeCasimirCompatibleData_iff hO hD x.1).1 x.2
    (Sum.inr (Sum.inl ((ncut,mcut),u,v)))

lemma physicalDegreeCasimirCompatibleData_adjoint
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) :
    degreeAdjointScalarL hO hD ij f g x.1 = 0 :=
  (mem_physicalDegreeCasimirCompatibleData_iff hO hD x.1).1 x.2
    (Sum.inr (Sum.inr (ij,f,g)))

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeCasimirConstraintL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.mem_physicalDegreeCasimirCompatibleData_iff
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.isClosed_physicalDegreeCasimirCompatibleData
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_isClosed
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_endpoint
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_casimir
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirCompatibleData_adjoint
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
