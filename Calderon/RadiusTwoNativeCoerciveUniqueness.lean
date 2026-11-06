import Calderon.RadiusTwoNativeEnergyConstructor
import Calderon.CoerciveSourceFunctionalMinimizer

/-! EXPANSION.json precedes fixed-native generic coercive uniqueness normalization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma eq_of_radiusTwoCoerciveSourceFunctional_eq_min
    (A : RadiusTwoH1Zero →L[ℝ] RadiusTwoH1Zero →L[ℝ] ℝ)
    (F : StrongDual ℝ RadiusTwoH1Zero)
    (hCo : IsCoercive A) (hSym : ∀ v w : RadiusTwoH1Zero, A v w = A w v)
    (u : RadiusTwoH1Zero) (hSolve : ∀ v : RadiusTwoH1Zero, A u v = F v)
    (v : RadiusTwoH1Zero)
    (hEqual : coerciveSourceFunctional A F v = coerciveSourceFunctional A F u) : v = u := by
  have hGen := eq_of_coerciveSourceFunctional_eq_min (V := RadiusTwoH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hGen
  exact hGen A F hCo hSym u hSolve v hEqual

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eq_of_radiusTwoCoerciveSourceFunctional_eq_min
