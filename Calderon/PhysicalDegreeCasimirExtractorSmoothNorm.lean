import Calderon.PhysicalDegreeCasimirHalfExtractor
import Mathlib.Analysis.Calculus.ContDiff.Basic
set_option autoImplicit false
noncomputable section
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic DirichletFamily.DriftBootstrap
/-! Same canonical extractor and restricted norm: cache generic calculus before actualmap;
use literal norm_coe equality. -/

lemma contDiff_compatibleDegreeHalfExtractorL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ContDiff ℝ ∞ (compatibleDegreeHalfExtractorL hO hD :
      physicalDegreeCasimirCompatibleData hO hD →
        SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) := by
  have hSmooth := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := physicalDegreeCasimirCompatibleData hO hD)
    (F := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTRACTOR_CONTDIFF_GENERIC_CACHED"; out.flush
  try simp only [physicalDegreeCasimirCompatibleData_topologicalSpace_eq,
    physicalDegreeCasimirCompatibleData_addCommMonoid_eq_standard,
    physicalDegreeCasimirCompatibleData_module_eq_standard,
    real_nontriviallyNormedField_normedField_eq,
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
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTRACTOR_CONTDIFF_GENERIC_NORMALIZED"; out.flush
  exact hSmooth (compatibleDegreeHalfExtractorL hO hD)

lemma norm_compatibleDegreeCasimirData_eq_of_coe_eq
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (y : PhysicalDegreeCasimirData)
    (hxy : (x : PhysicalDegreeCasimirData) = y) : ‖x‖ = ‖y‖ := by
  calc
    ‖x‖ = ‖(x : PhysicalDegreeCasimirData)‖ :=
      (physicalDegreeCasimirCompatibleData_norm_coe hO hD x).symm
    _ = ‖y‖ := congrArg (fun z : PhysicalDegreeCasimirData => ‖z‖) hxy

lemma norm_compatibleDegreeHalfExtractorL_apply_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    ‖compatibleDegreeHalfExtractorL hO hD x‖ ≤ 12*Real.sqrt 2*‖x‖ := by
  have hBound := norm_compatibleDegreeHalfExtension_le hO hD
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTENSION_NORM_UNIVERSAL_CACHED"; out.flush
  try simp only [physicalDegreeCasimirCompatibleData_topologicalSpace_eq,
    physicalDegreeCasimirCompatibleData_addCommMonoid_eq_standard,
    physicalDegreeCasimirCompatibleData_module_eq_standard,
    real_nontriviallyNormedField_normedField_eq,
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
    clm_normedSpace_module_eq] at hBound
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTENSION_NORM_UNIVERSAL_NORMALIZED"; out.flush
  have hValue := compatibleDegreeHalfExtractorL_apply hO hD x
  have hNorm := congrArg
    (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => ‖T‖) hValue
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTRACTOR_VALUE_NORM_EQ_READY"; out.flush
  have hPoint := hBound x
  run_tac do let out ← IO.getStdout; out.putStrLn "EXTENSION_POINT_NORM_BOUND_READY"; out.flush
  exact hNorm.le.trans hPoint

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.contDiff_compatibleDegreeHalfExtractorL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegreeCasimirData_eq_of_coe_eq
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegreeHalfExtractorL_apply_le
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
