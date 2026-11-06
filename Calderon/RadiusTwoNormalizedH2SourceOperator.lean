import Calderon.RadiusTwoNormalizedStrongSourceOperator
import Calderon.NativeStrongH2OperatorInclusion

/-! EXPANSION.json precedes the exact original root after actual/source-free partition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] TauCeti.sobolevStage radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem exists_radiusTwoNormalizedH2SourceOperator
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ R : RadiusTwoL2 →L[ℝ] BallSobolev 2, ∀ f : RadiusTwoL2,
      TauCeti.Wkp.firstOrder 1 (R f) =
        (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1) := by
  have hForget := exists_nativeH2_operator_of_strong_projection
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hForget
  trace "CACHED GENERIC INCLUSION NORMALIZED"
  obtain ⟨R,hR⟩ := exists_radiusTwoNormalizedStrongSourceOperator hreg g hg
  trace "ACTUAL STRONG SOURCE HEAD OBTAINED"
  let T : RadiusTwoL2 →L[ℝ] BallH1Zero :=
    radiusTwoNativeZeroDilation.comp (radiusTwoSourceSolutionL g hg)
  have hData : ∃ R2 : RadiusTwoL2 →L[ℝ] BallSobolev 2, ∀ f : RadiusTwoL2,
      TauCeti.Wkp.firstOrder 1 (R2 f) = (T f : BallH1) := hForget T R hR
  trace "GENERIC INCLUSION TYPED"
  refine Exists.elim hData ?_
  intro R2 hR2
  trace "SOURCE FREE NATIVE H2 INCLUSION OBTAINED"
  refine ⟨R2,?_⟩
  intro f
  have hT : T f = radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) := by
    simp only [T,ContinuousLinearMap.comp_apply,radiusTwoSourceSolutionL_apply]
  have hSource := congrArg Subtype.val hT
  with_reducible exact (hR2 f).trans hSource

end OAI.AnisotropicCalderon.ExteriorSource
