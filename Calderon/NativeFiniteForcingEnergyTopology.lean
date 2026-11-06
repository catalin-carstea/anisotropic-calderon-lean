import Calderon.NativeFiniteClmSandwichTopology
import Calderon.NativeFiniteForcingValue
import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
private abbrev nativeStrongDualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual ℝ BallH1Zero) :=
  NormedAddCommGroup.ofSeparation (fun (f : StrongDual ℝ BallH1Zero) (hf : ‖f‖ = 0) => by
    apply ContinuousLinearMap.ext
    intro v
    change f v = 0
    apply norm_le_zero_iff.mp
    calc
      ‖f v‖ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
      _ = 0 := by rw [hf, zero_mul])

attribute [local instance] nativeStrongDualNormedAddCommGroup

theorem contDiff_nativeFiniteForcingEnergy
    (J : BallH1Zero →L[ℝ] BallH1)
    (D : Fin 3 → BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (value : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (M : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (Mc : Fin 3 → (ℝ × (R3 × ℝ)) → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hM : ∀ i j : Fin 3, ContDiff ℝ ∞ (M i j))
    (hMc : ∀ i : Fin 3, ContDiff ℝ ∞ (Mc i)) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (∑ i : Fin 3, ∑ j : Fin 3,
        (forcingFromValueL ((D i).comp J)).comp ((M i j p).comp (D j))) +
        ∑ i : Fin 3, (forcingFromValueL (value.comp J)).comp ((Mc i p).comp (D i))) := by
  have hT := contDiff_nativeFiniteClmSandwich
    D (fun i => nativeFiniteForcingValueL J (D i))
    (nativeFiniteForcingValueL J value) M Mc hM hMc
  simpa only [nativeFiniteForcingValueL_eq, real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using hT

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
