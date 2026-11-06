import Calderon.RadiusTwoNativeStrongH2WeakBoundedOperator
import Calderon.NativeStrongH2BoundedPackaging
import Calderon.RadiusTwoBoundedNormalizedH2Source
import Calderon.NativeStrongH2SolutionConstruction

/-! EXPANSION.json precedes this actual bounded H2 source realization.
The existing regularity proposition remains explicit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] TauCeti.sobolevStage
  radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem exists_radiusTwoNormalizedStrongSourceOperator
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ R : RadiusTwoL2 →L[ℝ] StrongDirichletSpace 0,
      (strongDirichletProjectionL 0).comp R =
        radiusTwoNativeZeroDilation.comp (radiusTwoSourceSolutionL g hg) := by
  trace "PROOFENTER strong-domain actual H2 source operator"
  have hBuild := exists_radiusTwoNativeStrongH2_operator_of_weak_bounded_solve
  trace "CACHED SOURCE FREE COMBINED OPERATOR"
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hBuild
  trace "CACHED COMBINED OPERATOR DICTIONARIES NORMALIZED"
  let B : RadiusTwoL2 → BallH1Zero := fun f =>
    radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)
  let T : RadiusTwoL2 →L[ℝ] BallH1Zero :=
    radiusTwoNativeZeroDilation.comp (radiusTwoSourceSolutionL g hg)
  have hT : ∀ f : RadiusTwoL2, T f =
      radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) := by
    intro f
    simp only [T,ContinuousLinearMap.comp_apply,radiusTwoSourceSolutionL_apply]
  obtain ⟨C,hC,hSolve⟩ := exists_uniformly_bounded_normalizedH2_radiusTwoSource hreg g hg
  trace "ACTUAL UNIFORM GAIN actual H2 source operator"
  have hSolveB : ∀ f : RadiusTwoL2, ∃ U : BallSobolev 2,
      TauCeti.Wkp.firstOrder 1 U = (B f : BallH1) ∧ ‖U‖ ≤ C * ‖f‖ := hSolve
  trace "ACTUAL QUANTITATIVE PREMISE CACHED"
  have hTB : ∀ f : RadiusTwoL2, T f = B f := hT
  trace "ACTUAL MAP EQUALITY CACHED"
  have hResult : ∃ R : RadiusTwoL2 →L[ℝ] StrongDirichletSpace 0,
      (strongDirichletProjectionL 0).comp R = T ∧ ‖R‖ ≤ C := by
    trace "ENTER EXPLICIT ACTUAL OPERATOR RESULT APPLICATION"
    with_reducible exact hBuild B T hTB C hC hSolveB
  trace "EXPLICIT ACTUAL OPERATOR RESULT CACHED"
  obtain ⟨R,hR,hRNorm⟩ := hResult
  trace "BOUNDED STRONG OPERATOR actual H2 source operator"
  refine ⟨R,?_⟩
  with_reducible exact hR

end OAI.AnisotropicCalderon.ExteriorSource
