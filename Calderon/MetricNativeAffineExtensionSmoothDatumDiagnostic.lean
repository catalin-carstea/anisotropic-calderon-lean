import Calderon.MetricNativeAffineExtensionContinuityDiagnostic

/-! EXPANSION.json precedes this exact focused extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma metricNativeAffineHarmonicExtension_smoothSobolev
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : SmoothData) :
    metricNativeAffineHarmonicExtension g hg (smoothSobolev f) = metricDirichletSolution g hg f := rfl

end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineHarmonicExtension_smoothSobolev
