import Calderon.RadiusTwoWeakSourceAdditionEquation

/-! EXPANSION.json precedes this equation/uniqueness derivation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolution_add (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f h : RadiusTwoL2) :
    radiusTwoSourceSolution g hg (f + h) =
      radiusTwoSourceSolution g hg f + radiusTwoSourceSolution g hg h := by
  symm
  apply eq_radiusTwoSourceSolution g hg (f + h)
  intro v
  exact radiusTwoWeakSource_add_equation g hg (radiusTwoSourceSolution g hg)
    (radiusTwoSourceSolution_equation g hg) f h v

end OAI.AnisotropicCalderon.ExteriorSource
