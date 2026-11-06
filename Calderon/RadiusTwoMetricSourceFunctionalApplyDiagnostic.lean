import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeMetricEnergySymmetry
import Calderon.CoerciveSourceFunctionalMinimizer
import Calderon.RadiusTwoMetricSourceFunctionalDefinitionDiagnostic

/-! EXPANSION.json was saved before this exact focused extraction. Diagnostic only. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoMetricSourceFunctional_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero) :
    radiusTwoMetricSourceFunctional g hg F v =
      (1/2 : ℝ) * TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
        (v : RadiusTwoH1) (v : RadiusTwoH1) -
      ∫ x in radiusTwoOpens, F.1 x * TauCeti.W1p.value (v : RadiusTwoH1) x ∂(volume : Measure R3) := by
  have hE := TauCeti.PDE.energyFormH1L0_apply (memLp_radiusTwoMetricEnergyIntegrand g hg) v v
  have hF : TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F) v =
      ∫ x in radiusTwoOpens, F.1 x * TauCeti.W1p.value (v : RadiusTwoH1) x ∂(volume : Measure R3) := by
    rw [TauCeti.PDE.dirichletForcing_apply_eq_setIntegral]
    apply integral_congr_ae
    filter_upwards [smoothRadiusTwoForcing_ae F] with x hx
    rw [hx]
  exact congrArg₂ (fun a b : ℝ => (1/2 : ℝ)*a-b) hE hF


end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricSourceFunctional_apply
