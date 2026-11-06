import Calderon.NativeStrongH2SolutionConstruction
import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes exact source-free native strong-to-H2 packaging. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_nativeH2_operator_of_strong_projection
    (T : RadiusTwoL2 →L[ℝ] BallH1Zero)
    (R : RadiusTwoL2 →L[ℝ] StrongDirichletSpace 0)
    (hR : (strongDirichletProjectionL 0).comp R = T) :
    ∃ R2 : RadiusTwoL2 →L[ℝ] BallSobolev 2, ∀ f : RadiusTwoL2,
      TauCeti.Wkp.firstOrder 1 (R2 f) = (T f : BallH1) := by
  let I : StrongDirichletSpace 0 →L[ℝ] BallSobolev 2 :=
    (strongDirichletSubmodule 0).toSubmodule.subtypeL
  let R2 : RadiusTwoL2 →L[ℝ] BallSobolev 2 := I.comp R
  refine ⟨R2,?_⟩
  intro f
  have hR2f : R2 f = (R f : BallSobolev 2) := rfl
  have hRf0 := DFunLike.congr_fun hR f
  try simp only [ContinuousLinearMap.comp_apply] at hRf0
  have hRfH1 := congrArg Subtype.val hRf0
  have hStored := strongDirichletProjectionL_apply 0 (R f)
  trace "SOURCE FREE STORED PROJECTION JOIN TYPE EVIDENCE"
  trace_state
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hRfH1 hStored
  trace "SOURCE FREE STORED PROJECTION TYPES NORMALIZED"
  have hProjection := hStored.symm.trans hRfH1
  trace "SOURCE FREE NATIVE H2 FIRST ORDER PROJECTION JOINED"
  rw [hR2f]
  exact hProjection

end OAI.AnisotropicCalderon.ExteriorSource
