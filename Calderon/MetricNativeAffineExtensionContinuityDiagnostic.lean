import Calderon.MetricNativeAffineExtensionDefinitionDiagnostic
import Calderon.NativeIntrinsicAffineContinuity

/-! EXPANSION.json precedes this exact focused extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma continuous_metricNativeAffineHarmonicExtension (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (metricNativeAffineHarmonicExtension g hg) := by
  unfold metricNativeAffineHarmonicExtension
  exact continuous_tauAffineSolution (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := principalCoefficient g) (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg)

end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.continuous_metricNativeAffineHarmonicExtension
