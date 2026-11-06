import Calderon.NativeStrongH2SolutionConstruction

/-! EXPANSION.json precedes native strong-domain bounded linear solve outside actual metric/source contexts. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_nativeStrongH2_operator_of_bounded_solve
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : Z →L[ℝ] BallH1Zero) (C : ℝ) (hC : 0 ≤ C)
    (hSolve : ∀ f : Z, ∃ V : StrongDirichletSpace 0,
      strongDirichletProjectionL 0 V = T f ∧ ‖V‖ ≤ C * ‖f‖) :
    ∃ R : Z →L[ℝ] StrongDirichletSpace 0,
      (strongDirichletProjectionL 0).comp R = T ∧ ‖R‖ ≤ C := by
  have hgSolve := exists_continuousLinearMap_of_bounded_solve
    (X := StrongDirichletSpace 0) (Y := BallH1Zero) (Z := Z)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hgSolve
  exact hgSolve (strongDirichletProjectionL 0) (strongDirichletProjectionL_injective 0)
    T C hC hSolve

end OAI.AnisotropicCalderon.ExteriorSource
