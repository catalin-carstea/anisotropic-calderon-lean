import Calderon.ParametricSobolevForm
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

/-! Full upfront: EXPANSION-correspondence-dictionary-diagnostic-v001.json.
One typed definition diagnostic; not a whole correspondence retry. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def unitBallEnergyForm_dictionaryProbe
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) ((0 : R3 → R3) x)
      ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens)) :
    BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := by
  have hC := hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (a x)
    ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq] at hC
  have hForm := unitBallCoefficientFormL
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq, submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq] at hForm
  exact hForm hC

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallEnergyForm_dictionaryProbe
