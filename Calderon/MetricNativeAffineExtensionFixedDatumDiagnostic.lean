import Calderon.MetricNativeAffineExtensionSmoothDatumDiagnostic
import Calderon.NativeAffineForcingZero
import Calderon.NativeAffineCorrectionZero

/-! EXPANSION.json precedes this exact focused extraction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma metricNativeAffineHarmonicExtension_eq_self_of_weak
    (g : MatrixField) (hg : IsAdmissibleMetric g) (d : BallH1)
    (hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 d (v : BallH1) = 0) :
    metricNativeAffineHarmonicExtension g hg d = d := by
  have hForce := tauAffineForcing_eq_zero_of_energy_eq_zero
    (memLp_metricEnergyIntegrand g hg) d hWeak
  unfold metricNativeAffineHarmonicExtension
  exact tauAffineSolution_eq_self_of_forcing_eq_zero
    (memLp_metricEnergyIntegrand g hg) (isCoercive_metricEnergyForm g hg) d hForce


end OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource
#print axioms OAI.AnisotropicCalderon.EnergyBridge.ExteriorSource.metricNativeAffineHarmonicExtension_eq_self_of_weak
