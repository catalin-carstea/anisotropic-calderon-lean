import Calderon.MetricDirichletReplacementCorrection

/-! EXPANSION.json precedes this exact focused extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def metricNativeAffineHarmonicExtension (g : MatrixField) (hg : IsAdmissibleMetric g)
    (d : BallH1) : BallH1 :=
  tauAffineSolution (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg) d


end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineHarmonicExtension
