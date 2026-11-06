import Calderon.MetricNativeAffineExtensionFixedDatumDiagnostic

/-! EXPANSION.json precedes this exact focused tail extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma continuous_metricNativeAffineHarmonicExtension_self_energy
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    Continuous (fun d : BallH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (metricNativeAffineHarmonicExtension g hg d) (metricNativeAffineHarmonicExtension g hg d)) := by
  let E : BallH1 →L[ℝ] BallH1 →L[ℝ] ℝ :=
    TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := principalCoefficient g) (b := 0) (c := 0) (memLp_metricEnergyIntegrand g hg)
  have hH := continuous_metricNativeAffineHarmonicExtension g hg
  have hQ : Continuous (fun d : BallH1 => E (metricNativeAffineHarmonicExtension g hg d)
      (metricNativeAffineHarmonicExtension g hg d)) := (E.continuous.comp hH).clm_apply hH
  have hIdent : (fun d : BallH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (metricNativeAffineHarmonicExtension g hg d) (metricNativeAffineHarmonicExtension g hg d)) =
      (fun d : BallH1 => E (metricNativeAffineHarmonicExtension g hg d)
        (metricNativeAffineHarmonicExtension g hg d)) := by
    funext d
    exact (TauCeti.PDE.energyFormH1L_apply (memLp_metricEnergyIntegrand g hg) _ _).symm
  exact hIdent.symm ▸ hQ


end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.continuous_metricNativeAffineHarmonicExtension_self_energy
