import Calderon.NativeCoefficientWeakInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem nativeZeroFunctionalInverse_scalar_equation_of_coercive
    (B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hB : IsCoercive B)
    (ell : StrongDual ℝ BallH1Zero) (v : BallH1Zero) :
    B (nativeZeroFunctionalInverse B ell) v = ell v := by
  have hg := apply_functionalInverse (V := BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hg
  have hEq := congrArg (fun z : BallH1Zero => B z v) (nativeZeroFunctionalInverse_apply B ell)
  exact hEq.trans (hg B hB ell v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroFunctionalInverse_scalar_equation_of_coercive
