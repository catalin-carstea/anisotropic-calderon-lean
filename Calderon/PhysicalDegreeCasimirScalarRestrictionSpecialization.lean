import Calderon.PhysicalDegreeCasimirNormalizedRestrictionCache
import Calderon.PhysicalDegreeCasimirKernelSmoothnessTransportCache
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic ClosedScalarCompatibility DirichletFamily.DriftBootstrap
/-! Actual-space specialization; the concrete function and set are inferred
from the typed proof, with no reconstructed instances. -/

def physicalDegreeCasimirScalarRestrictionCoeCache
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) := id (by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hValue := physicalDegreeCasimirRestrictionCoeNormalizedCache (X := X) (I := ConstraintIndex)
  have hActualValue := hValue (degreeCasimirConstraintL hO hD)
  run_tac do let out ← IO.getStdout; out.putStrLn "ACTUAL_SCALAR_COE_UNIVERSAL_READY"; out.flush
  exact hActualValue)

def physicalDegreeCasimirScalarRestrictionSmoothness
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (f : X → PhysicalDegreeCasimirData) (s : Set X) (hs : IsOpen s)
    (hOriginal : ∀ x ∈ s, ∀ z, degreeCasimirConstraintL hO hD z (f x) = 0)
    (hf : ContDiffOn ℝ ∞ f s) := id (by
  let ConstraintIndex : Type := ((Σ m : ℕ, SphereSobolev (3/2:ℝ) × harmonicSphereSubspace m) ⊕
      (((ℕ × ℕ) × (∀ k, harmonicSphereSubspace k) × (∀ k, harmonicSphereSubspace k)) ⊕
        ((Fin 3 × Fin 3) × SphereSobolev 1 × SphereSobolev 1)))
  have hTransport := physicalDegreeCasimirKernelSmoothnessTransportCache (X := X) hO hD
  have hSmooth := physicalDegreeCasimirRestrictionSmoothnessNormalizedCache (X := X) (I := ConstraintIndex)
  run_tac do let out ← IO.getStdout; out.putStrLn "ACTUAL_SCALAR_PARENTS_READY"; out.flush
  have hF := hf
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
      clm_normedSpace_module_eq] at hF
  run_tac do let out ← IO.getStdout; out.putStrLn "ACTUAL_SCALAR_AMBIENT_READY"; out.flush
  have hStandard := hSmooth (degreeCasimirConstraintL hO hD) f s hs hOriginal hF
  run_tac do let out ← IO.getStdout; out.putStrLn "ACTUAL_SCALAR_STANDARD_READY"; out.flush
  have hActual := hTransport _ _ hStandard
  run_tac do let out ← IO.getStdout; out.putStrLn "ACTUAL_SCALAR_TRANSPORTED"; out.flush
  exact hActual)

#check @physicalDegreeCasimirScalarRestrictionCoeCache
#check @physicalDegreeCasimirScalarRestrictionSmoothness
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirScalarRestrictionCoeCache
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.physicalDegreeCasimirScalarRestrictionSmoothness
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
