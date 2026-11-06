import Calderon.NativeStrongH2BoundedOperator
import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes this source-free actual L2 specialization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoNativeStrongH2_operator_of_bounded_solve
    (T : RadiusTwoL2 →L[ℝ] BallH1Zero) (C : ℝ) (hC : 0 ≤ C)
    (hSolve : ∀ f : RadiusTwoL2, ∃ V : StrongDirichletSpace 0,
      strongDirichletProjectionL 0 V = T f ∧ ‖V‖ ≤ C * ‖f‖) :
    ∃ R : RadiusTwoL2 →L[ℝ] StrongDirichletSpace 0,
      (strongDirichletProjectionL 0).comp R = T ∧ ‖R‖ ≤ C := by
  trace "PROOFENTER source-free radius-two L2 strong operator"
  have hGeneric := exists_nativeStrongH2_operator_of_bounded_solve (Z := RadiusTwoL2)
  trace "ACTUAL L2 SOURCE SPECIALIZED strong operator"
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGeneric
  trace "ACTUAL L2 SOURCE NORMALIZED strong operator"
  exact hGeneric T C hC hSolve

end OAI.AnisotropicCalderon.ExteriorSource
