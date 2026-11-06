import Calderon.RealHarmonicInheritedStructureData

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
