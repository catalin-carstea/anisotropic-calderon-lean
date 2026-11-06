import Calderon.MetricNativeAffineEnergyContinuityDiagnostic
import Calderon.NativeGlobalSmoothH1Density

/-! EXPANSION.json precedes this exact focused tail extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

open OAI.AnisotropicCalderon.DirichletFamily
lemma metricNativeAffineHarmonicExtension_self_energy_eq_of_minimalEnergy_eq
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (d : BallH1) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0
      (metricNativeAffineHarmonicExtension g₂ hg₂ d) (metricNativeAffineHarmonicExtension g₂ hg₂ d) =
    TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0
      (metricNativeAffineHarmonicExtension g₁ hg₁ d) (metricNativeAffineHarmonicExtension g₁ hg₁ d) := by
  refine denseRange_smoothSobolev.induction_on d
    (isClosed_eq (continuous_metricNativeAffineHarmonicExtension_self_energy g₂ hg₂)
      (continuous_metricNativeAffineHarmonicExtension_self_energy g₁ hg₁)) ?_
  intro f
  change TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0
      (metricDirichletSolution g₂ hg₂ f) (metricDirichletSolution g₂ hg₂ f) =
    TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0
      (metricDirichletSolution g₁ hg₁ f) (metricDirichletSolution g₁ hg₁ f)
  exact metricDirichletSolution_self_energy_eq_of_minimalEnergy_eq g₁ g₂ hg₁ hg₂ hΛ f


end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineHarmonicExtension_self_energy_eq_of_minimalEnergy_eq
