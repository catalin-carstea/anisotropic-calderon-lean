import Calderon.RadiusTwoNativeEnergyEvaluation
import Calderon.RadiusTwoMetricSourceFunctionalApplyDiagnostic

/-! EXPANSION.json precedes exact actual native energy/source/functional correspondence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoMetricEnergyL0Normalized_comm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (u v : RadiusTwoH1Zero) :
    radiusTwoMetricEnergyL0Normalized g hg u v = radiusTwoMetricEnergyL0Normalized g hg v u := by
  exact (radiusTwoMetricEnergyL0Normalized_apply g hg u v).trans
    ((radiusTwoMetricEnergy_symm g hg u v).trans
      (radiusTwoMetricEnergyL0Normalized_apply g hg v u).symm)

lemma radiusTwoMetricEnergyL0Normalized_source_equation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero) :
    radiusTwoMetricEnergyL0Normalized g hg
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) v =
      TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F) v := by
  exact (radiusTwoMetricEnergyL0Normalized_apply g hg
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) v).trans
      (radiusTwoSourceSolution_equation g hg (smoothRadiusTwoForcing F) v)

lemma radiusTwoMetricSourceFunctional_eq_normalizedEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero) :
    radiusTwoMetricSourceFunctional g hg F v =
      coerciveSourceFunctional (radiusTwoMetricEnergyL0Normalized g hg)
        (TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F)) v := by
  unfold radiusTwoMetricSourceFunctional coerciveSourceFunctional
  exact congrArg (fun t : ℝ => (1/2 : ℝ)*t-
    TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F) v)
      (radiusTwoMetricEnergyL0Normalized_apply_eq_raw g hg v v).symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergyL0Normalized_comm
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricEnergyL0Normalized_source_equation
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricSourceFunctional_eq_normalizedEnergy
