import Calderon.RadiusTwoNativeSourceSolution

/-! EXPANSION.json precedes this equation/uniqueness derivation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolution_smul (g : MatrixField) (hg : IsAdmissibleMetric g)
    (c : ℝ) (f : RadiusTwoL2) :
    radiusTwoSourceSolution g hg (c • f) = c • radiusTwoSourceSolution g hg f := by
  symm
  apply eq_radiusTwoSourceSolution g hg (c • f)
  intro v
  simp only [Submodule.coe_smul]
  rw [TauCeti.PDE.energyFormH1_smul_left (a := principalCoefficient g)
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (r := c)
    (u := (radiusTwoSourceSolution g hg f : RadiusTwoH1)) (v := (v : RadiusTwoH1)),
    radiusTwoSourceSolution_equation]
  simp only [TauCeti.PDE.dirichletForcing_apply,inner_smul_left,conj_trivial,smul_eq_mul]


end OAI.AnisotropicCalderon.ExteriorSource
