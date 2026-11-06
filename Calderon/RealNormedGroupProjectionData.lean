import Calderon.RealHarmonicInheritedStructureData

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
STRONG-CANONICAL-REAL-GROUP-METRIC-PROJECTIONS-UPFRONT-v001.md. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

@[defeq] theorem real_normedAddCommGroup_addGroup_eq_natural :
    Real.normedAddCommGroup.toAddCommGroup.toAddGroup = Real.instAddGroup := rfl

@[defeq] theorem real_normedAddCommGroup_pseudoMetricSpace_eq_natural :
    Real.normedAddCommGroup.toSeminormedAddCommGroup.toPseudoMetricSpace =
      Real.pseudoMetricSpace := rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_normedAddCommGroup_addGroup_eq_natural
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.real_normedAddCommGroup_pseudoMetricSpace_eq_natural
