import Calderon.PhysicalDegreeCasimirScalarFunctionalsCore
import Calderon.PhysicalDegreeAdjointProjectionEvaluation
import Calderon.InnerIsometryOperatorEvaluation
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic InnerIsometryOperatorEvaluation DirichletFamily.DriftBootstrap
/-! Evaluation of an additional actual scalar term. -/
attribute [local irreducible] sphereSobolevZeroEquiv sphereSobolevInclusionL
  degreeAdjointProjectionL
lemma degreeAdjointScalarTerm_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ij : Fin 3 × Fin 3) (f g : SphereSobolev 1) (x : PhysicalDegreeCasimirData) :
    let Z : SphereSobolev 0 ≃ₗᵢ[ℝ] SphereL2 := (sphereSobolevZeroEquiv hO hD).symm
    let a0 : SphereL2 := Z (sphereSobolevInclusionL 1 0 (by norm_num) f)
    ((innerSL ℝ a0).comp (Z.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))) x =
      ⟪a0,Z (x.2.2 ij g)⟫_ℝ := by
  dsimp only
  let Z : SphereSobolev 0 ≃ₗᵢ[ℝ] SphereL2 := (sphereSobolevZeroEquiv hO hD).symm
  let a0 : SphereL2 := Z (sphereSobolevInclusionL 1 0 (by norm_num) f)
  run_tac do let out ← IO.getStdout; out.putStrLn "ADJOINT_SCALAR_Z_TYPED"; out.flush
  have hGeneric := innerSL_linear_isometry_equiv_eval_comp_apply
    (X := PhysicalDegreeCasimirData) (U := SphereSobolev 1)
    (V := SphereSobolev 0) (W := SphereL2)
  try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  run_tac do let out ← IO.getStdout; out.putStrLn "ADJOINT_SCALAR_GENERIC_TYPED"; out.flush
  have hEvalTerm :
      ((innerSL ℝ a0).comp (Z.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))) x =
      ⟪a0,Z ((degreeAdjointProjectionL ij x) g)⟫_ℝ := by
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq]
    exact hGeneric Z a0 g (degreeAdjointProjectionL ij) x
  run_tac do let out ← IO.getStdout; out.putStrLn "ADJOINT_SCALAR_TERM_EVALUATED"; out.flush
  have hTerm :
      ((innerSL ℝ a0).comp (Z.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℝ (SphereSobolev 0) g).comp (degreeAdjointProjectionL ij)))) x =
      ⟪a0,Z (x.2.2 ij g)⟫_ℝ :=
    hEvalTerm.trans (congrArg
      (fun Q : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => ⟪a0,Z (Q g)⟫_ℝ)
      (degreeAdjointProjectionL_apply ij x))
  run_tac do let out ← IO.getStdout; out.putStrLn "ADJOINT_SCALAR_PROJECTION_TRANSPORTED"; out.flush
  exact hTerm

#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeAdjointScalarTerm_apply
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
