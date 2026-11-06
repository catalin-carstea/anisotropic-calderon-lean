import Calderon.FiniteForcingEnergy
import Calderon.CoordinateFluxEnergy
import Calderon.InheritedNormedStructureData
import Calderon.LpInheritedStructureData
import Calderon.ClmInheritedStructureData

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

/-! Full upfront expansion: EXPANSION-native-smooth-full-energy-and-angle-family-v001.json.
Generic finite composition is specialized before actual coefficient operators are inserted. -/

lemma contDiff_nativeFullFiniteForcingEnergy
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (M : Fin 3 → Fin 3 → P → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (Mc : Fin 3 → P → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hM : ∀ i j, ContDiff ℝ ∞ (M i j)) (hMc : ∀ i, ContDiff ℝ ∞ (Mc i)) :
    ContDiff ℝ ∞ (fun p =>
      (∑ i : Fin 3, ∑ j : Fin 3, (forcingFromValueL (unitBallCoordinateGradientL i)).comp
        ((M i j p).comp (unitBallCoordinateGradientL j))) +
      ∑ i : Fin 3, (forcingFromValueL
        (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))).comp
        ((Mc i p).comp (unitBallCoordinateGradientL i))) := by
  have hg := contDiff_finiteForcingEnergy (X := P) (U := BallH1) (V := BallH1)
    (H := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (ι := Fin 3)
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
  have h := hg (ContinuousLinearMap.id ℝ BallH1) unitBallCoordinateGradientL
    (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)) M Mc hM hMc
  simpa only [ContinuousLinearMap.comp_id] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeFullFiniteForcingEnergy
