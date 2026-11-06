import Calderon.RadiusTwoNativeSourceFoundation
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

/-! EXPANSION.json precedes this actual fixed-native energy constructor normalization probe. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def radiusTwoMetricEnergyL0Normalized (g : MatrixField) (hg : IsAdmissibleMetric g) :
    RadiusTwoH1Zero →L[ℝ] RadiusTwoH1Zero →L[ℝ] ℝ := by
  have hE := TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
    (a := principalCoefficient g) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (memLp_radiusTwoMetricEnergyIntegrand g hg)
  try dsimp only [TauCeti.PDE.instSeminormedAddCommGroupW1p,
    TauCeti.PDE.instNormedSpaceW1p] at hE
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq] at hE
  exact hE

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergyL0Normalized
