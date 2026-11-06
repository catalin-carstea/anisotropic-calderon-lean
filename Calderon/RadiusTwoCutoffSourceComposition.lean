import Calderon.RadiusTwoBoundedSourceOperator
import Calderon.RadiusTwoFixedRowCutoffForcingOperator

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSourceSolutionL_comp_cutoffForcing_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData)
    (L : RadiusTwoH1 →L[ℝ] RadiusTwoL2)
    (hL : ∀ u : RadiusTwoH1, L u = radiusTwoFixedRowCutoffForcingLp g hg η u)
    (w : RadiusTwoH1Zero) :
    ((radiusTwoSourceSolutionL g hg).comp
      (L.comp (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule.subtypeL)) w =
      radiusTwoSourceSolution g hg
        (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)) := by
  have hJ := Submodule.subtypeL_apply
    (TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule w
  have hInput : L
      ((TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule.subtypeL w) =
      radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1) :=
    (congrArg L hJ).trans (hL (w : RadiusTwoH1))
  change radiusTwoSourceSolutionL g hg
    (L ((TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2).toSubmodule.subtypeL w)) = _
  exact (congrArg (radiusTwoSourceSolutionL g hg) hInput).trans
    (radiusTwoSourceSolutionL_apply g hg _)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolutionL_comp_cutoffForcing_apply
