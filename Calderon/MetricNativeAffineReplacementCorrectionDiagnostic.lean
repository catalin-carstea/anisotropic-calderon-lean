import Calderon.MetricNativeAffineEnergyDensityDiagnostic

/-! EXPANSION.json precedes this exact focused tail extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def metricNativeAffineReplacementCorrection
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (d : BallH1) : BallH1Zero :=
  tauAffineCorrection (memLp_metricEnergyIntegrand g₂ hg₂) (isCoercive_metricEnergyForm g₂ hg₂) d -
    tauAffineCorrection (memLp_metricEnergyIntegrand g₁ hg₁) (isCoercive_metricEnergyForm g₁ hg₁) d

lemma metricNativeAffineReplacementCorrection_coe
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (d : BallH1) :
    (metricNativeAffineReplacementCorrection g₁ g₂ hg₁ hg₂ d : BallH1) =
      metricNativeAffineHarmonicExtension g₂ hg₂ d - metricNativeAffineHarmonicExtension g₁ hg₁ d := by
  unfold metricNativeAffineReplacementCorrection metricNativeAffineHarmonicExtension tauAffineSolution
  simp only [Submodule.coe_sub]
  abel

end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineReplacementCorrection
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineReplacementCorrection_coe
