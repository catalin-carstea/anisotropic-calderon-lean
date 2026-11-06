import Calderon.RadiusTwoNativeSourceSolution

/-! EXPANSION.json precedes transparent weak-equation algebra; its equation
argument is discharged by the checked actual solver in the separate caller. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoWeakSource_add_equation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (u : RadiusTwoL2 → RadiusTwoH1Zero)
    (hEq : ∀ (f : RadiusTwoL2) (v : RadiusTwoH1Zero),
      TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
        (u f : RadiusTwoH1) (v : RadiusTwoH1) = TauCeti.PDE.dirichletForcing f v)
    (f h : RadiusTwoL2) (v : RadiusTwoH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      ((u f + u h : RadiusTwoH1Zero) : RadiusTwoH1) (v : RadiusTwoH1) =
        TauCeti.PDE.dirichletForcing (f+h) v := by
  calc
    _ = TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (u f : RadiusTwoH1) (v : RadiusTwoH1) +
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (u h : RadiusTwoH1) (v : RadiusTwoH1) := by
      simpa only [Submodule.coe_add] using
        TauCeti.PDE.energyFormH1_add_left (memLp_radiusTwoMetricEnergyIntegrand g hg)
          (u := (u f : RadiusTwoH1)) (v := (v : RadiusTwoH1)) (w := (u h : RadiusTwoH1))
    _ = TauCeti.PDE.dirichletForcing f v + TauCeti.PDE.dirichletForcing h v :=
      congrArg₂ (fun x y : ℝ => x+y) (hEq f v) (hEq h v)
    _ = TauCeti.PDE.dirichletForcing (f+h) v := by
      simp only [TauCeti.PDE.dirichletForcing_apply,inner_add_left]

end OAI.AnisotropicCalderon.ExteriorSource
