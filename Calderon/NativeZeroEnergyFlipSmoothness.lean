import Calderon.NativeZeroEnergyAdjointInverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma contDiff_bilinearFlipFamily {P V : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : P → V →L[ℝ] StrongDual ℝ V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun p => (A p).flip) := by
  let F : (V →L[ℝ] StrongDual ℝ V) →L[ℝ] (V →L[ℝ] StrongDual ℝ V) :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact F.contDiff.comp hA

lemma contDiff_nativeZeroEnergyFlipFamily {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun p => (A p).flip) := by
  have hg := contDiff_bilinearFlipFamily (P := P) (V := BallH1Zero)
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
  exact hg A hA

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_bilinearFlipFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeZeroEnergyFlipFamily
