import Calderon.PhysicalDegreeCasimirCompatibleRawGraph
import Calderon.PhysicalDegreeCasimirCanonicalProjectionComparison
import Calderon.SphereSobolevCompatibleEndpointInterpolation
import Calderon.SphereSobolevDegreeFormPointCompletion
import Calderon.DenseOperatorSignedTaylorCompletion
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic DirichletFamily.DriftBootstrap DenseOperatorTaylorCompletion
/-! GENUINELY derived canonical bounded-linear
half extractor. No desired bound, adjunction, or existence is assumed. -/

lemma norm_compatibleDegreeRawHighL_le_half_input
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (u : SphereSobolev (3/2:ℝ)) :
    ‖compatibleDegreeRawHighL hO hD x u‖ ≤
      (12*Real.sqrt 2*‖x‖)*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖ := by
  have hGeneric := exists_half_degree_extension_of_decoded_form_bound
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  have hExtension : ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ 12*Real.sqrt 2*‖x‖ ∧
      (∀ z, S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z) =
        compatibleDegreeRawHighL hO hD x z) ∧
      ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          ((m:ℝ)-(n:ℝ)) • compatibleDegreeSharpBlockL hO hD x m n z := by
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
    exact hGeneric (compatibleDegreeRawHighL hO hD x) (compatibleDegreeSharpBlockL hO hD x)
      (compatibleDegreeRawHighL_physical_harmonic_block hO hD x)
      (12*Real.sqrt 2*‖x‖) (by positivity) (compatibleDegree_finite_degree_half_bound hO hD x)
  obtain ⟨S,hNorm,hGraph,_⟩ := hExtension
  calc
    _ = ‖S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)‖ :=
      congrArg norm (hGraph u).symm
    _ ≤ ‖S‖*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖ := S.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)

def compatibleDegreeHalfExtension
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (compatibleDegreeRawHighL hO hD x).toLinearMap.extendOfNorm
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap

lemma compatibleDegreeHalfExtension_high_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (u : SphereSobolev (3/2:ℝ)) :
    compatibleDegreeHalfExtension hO hD x
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) =
        compatibleDegreeRawHighL hO hD x u :=
  DenseRealLinearExtension.extendOfNorm_apply_dense (compatibleDegreeRawHighL hO hD x).toLinearMap
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (12*Real.sqrt 2*‖x‖) (norm_compatibleDegreeRawHighL_le_half_input hO hD x) u

lemma norm_compatibleDegreeHalfExtension_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    ‖compatibleDegreeHalfExtension hO hD x‖ ≤ 12*Real.sqrt 2*‖x‖ := by
  apply (compatibleDegreeHalfExtension hO hD x).opNorm_le_bound (by positivity)
  intro u
  exact DenseRealLinearExtension.norm_extendOfNorm_apply_dense
    (compatibleDegreeRawHighL hO hD x).toLinearMap
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).toLinearMap
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (12*Real.sqrt 2*‖x‖) (norm_compatibleDegreeRawHighL_le_half_input hO hD x) u

lemma compatibleDegreeHalfExtension_add
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x y : physicalDegreeCasimirCompatibleData hO hD) :
    compatibleDegreeHalfExtension hO hD (x+y) =
      compatibleDegreeHalfExtension hO hD x + compatibleDegreeHalfExtension hO hD y := by
  apply dense_operator_extension_unique
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  intro u
  have hRaw : compatibleDegreeRawHighL hO hD (x+y) u =
      compatibleDegreeRawHighL hO hD x u + compatibleDegreeRawHighL hO hD y u :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (degreeRawHighDataL.map_add x.1 y.1)
  calc
    _ = compatibleDegreeRawHighL hO hD (x+y) u := compatibleDegreeHalfExtension_high_graph hO hD (x+y) u
    _ = compatibleDegreeRawHighL hO hD x u + compatibleDegreeRawHighL hO hD y u := hRaw
    _ = compatibleDegreeHalfExtension hO hD x
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) +
        compatibleDegreeHalfExtension hO hD y
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) :=
      congrArg₂ (fun z w : SphereSobolev (-(1/2:ℝ)) => z+w)
        (compatibleDegreeHalfExtension_high_graph hO hD x u).symm
        (compatibleDegreeHalfExtension_high_graph hO hD y u).symm
    _ = _ := rfl

lemma compatibleDegreeHalfExtension_smul
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : ℝ) (x : physicalDegreeCasimirCompatibleData hO hD) :
    compatibleDegreeHalfExtension hO hD (c • x) = c • compatibleDegreeHalfExtension hO hD x := by
  apply dense_operator_extension_unique
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  intro u
  have hRaw : compatibleDegreeRawHighL hO hD (c • x) u =
      c • compatibleDegreeRawHighL hO hD x u :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T u)
      (degreeRawHighDataL.map_smul c x.1)
  calc
    _ = compatibleDegreeRawHighL hO hD (c • x) u := compatibleDegreeHalfExtension_high_graph hO hD (c • x) u
    _ = c • compatibleDegreeRawHighL hO hD x u := hRaw
    _ = c • compatibleDegreeHalfExtension hO hD x
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) :=
      congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => c • z)
        (compatibleDegreeHalfExtension_high_graph hO hD x u).symm
    _ = _ := rfl

local instance compatibleDegreeHalfExtractorOperatorNorm
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    Norm (physicalDegreeCasimirCompatibleData hO hD →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))) := by
  have hNorm := ContinuousLinearMap.hasOpNorm
    (E := physicalDegreeCasimirCompatibleData hO hD)
    (F := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (σ₁₂ := RingHom.id ℝ)
  simpa only [physicalDegreeCasimirCompatibleData_topologicalSpace_eq,
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
    clm_normedSpace_module_eq] using hNorm

def compatibleDegreeHalfExtractorL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    physicalDegreeCasimirCompatibleData hO hD →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) := by
  let A : physicalDegreeCasimirCompatibleData hO hD →ₗ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    { toFun := compatibleDegreeHalfExtension hO hD
      map_add' := compatibleDegreeHalfExtension_add hO hD
      map_smul' := compatibleDegreeHalfExtension_smul hO hD }
  have hConstructor := sphereInterpolationBoundedLinearMap
    (X := physicalDegreeCasimirCompatibleData hO hD)
    (Y := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
  run_tac do let out ← IO.getStdout; out.putStrLn "HALF_EXTRACTOR_CONSTRUCTOR_CACHED"; out.flush
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
    clm_normedSpace_module_eq] at hConstructor
  run_tac do let out ← IO.getStdout; out.putStrLn "HALF_EXTRACTOR_CONSTRUCTOR_NORMALIZED"; out.flush
  exact hConstructor A (12*Real.sqrt 2) (norm_compatibleDegreeHalfExtension_le hO hD)

lemma compatibleDegreeHalfExtractorL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) :
    compatibleDegreeHalfExtractorL hO hD x = compatibleDegreeHalfExtension hO hD x := rfl

lemma compatibleDegreeHalfExtractorL_high_graph
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (x : physicalDegreeCasimirCompatibleData hO hD) (u : SphereSobolev (3/2:ℝ)) :
    compatibleDegreeHalfExtractorL hO hD x
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) =
        compatibleDegreeRawHighL hO hD x u :=
  compatibleDegreeHalfExtension_high_graph hO hD x u

lemma norm_compatibleDegreeHalfExtractorL_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ‖compatibleDegreeHalfExtractorL hO hD‖ ≤ 12*Real.sqrt 2 := by
  have hBound := ContinuousLinearMap.opNorm_le_bound
    (E := physicalDegreeCasimirCompatibleData hO hD)
    (F := SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (σ₁₂ := RingHom.id ℝ)
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
  apply hBound (compatibleDegreeHalfExtractorL hO hD) (by positivity)
  intro x
  change ‖compatibleDegreeHalfExtension hO hD x‖ ≤ (12*Real.sqrt 2)*‖x‖
  exact norm_compatibleDegreeHalfExtension_le hO hD x

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtractorOperatorNorm
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegreeRawHighL_le_half_input
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtension
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtension_high_graph
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegreeHalfExtension_le
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtension_add
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtension_smul
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtractorL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtractorL_apply
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.compatibleDegreeHalfExtractorL_high_graph
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.norm_compatibleDegreeHalfExtractorL_le
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
