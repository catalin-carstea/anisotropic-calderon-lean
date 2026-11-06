import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeMetricEnergySymmetry

/-! EXPANSION.json precedes reciprocity of the actual constructed source solutions. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolution_reciprocity (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f h : RadiusTwoL2) :
    ⟪f,TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1)⟫_ℝ =
      ⟪h,TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1)⟫_ℝ := by
  calc
    _ = TauCeti.PDE.dirichletForcing f (radiusTwoSourceSolution g hg h) :=
      (TauCeti.PDE.dirichletForcing_apply f (radiusTwoSourceSolution g hg h)).symm
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (radiusTwoSourceSolution g hg f : RadiusTwoH1) (radiusTwoSourceSolution g hg h : RadiusTwoH1) :=
      (radiusTwoSourceSolution_equation g hg f (radiusTwoSourceSolution g hg h)).symm
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (radiusTwoSourceSolution g hg h : RadiusTwoH1) (radiusTwoSourceSolution g hg f : RadiusTwoH1) :=
      radiusTwoMetricEnergy_symm g hg _ _
    _ = TauCeti.PDE.dirichletForcing h (radiusTwoSourceSolution g hg f) :=
      radiusTwoSourceSolution_equation g hg h (radiusTwoSourceSolution g hg f)
    _ = _ := TauCeti.PDE.dirichletForcing_apply h (radiusTwoSourceSolution g hg f)

end OAI.AnisotropicCalderon.ExteriorSource
