import Calderon.NativeCoefficientWeakEnergy
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.NativeParameterWeakLiftTopology

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma contDiff_nativeTwoAngle_dual_test_postcomposition
    (Q : StrongDual ℝ BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (E : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → BallH1 →L[ℝ] StrongDual ℝ BallH1)
    (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × (R3 × ℝ))) => Q.comp (E p)) := by
  have hGeneric := contDiff_fixed_postcomposition
    (P := ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U := BallH1)
    (V := StrongDual ℝ BallH1) (W := StrongDual ℝ BallH1Zero)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hGeneric
  exact hGeneric Q E hE

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeTwoAngle_dual_test_postcomposition
