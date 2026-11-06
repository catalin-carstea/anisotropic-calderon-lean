import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeMetricEnergySymmetry
import Calderon.CoerciveSourceFunctionalMinimizer

/-! EXPANSION.json was saved before this exact focused extraction. Diagnostic only. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def radiusTwoMetricSourceFunctional (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero) : ℝ :=
  coerciveSourceFunctional
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := radiusTwoOpens)
      (a := principalCoefficient g) (b := 0) (c := 0) (memLp_radiusTwoMetricEnergyIntegrand g hg))
    (TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F)) v


end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricSourceFunctional
