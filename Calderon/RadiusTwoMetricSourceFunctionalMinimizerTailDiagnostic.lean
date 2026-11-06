import Calderon.RadiusTwoMetricSourceFunctionalMinimumDiagnostic
import Calderon.ScalarFunctionalEqualityTransport
import Calderon.RadiusTwoNativeCoerciveUniqueness

/-! EXPANSION.json precedes this actual typed-energy min/unique specialization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma eq_radiusTwoSourceSolution_of_functional_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero)
    (hEqual : radiusTwoMetricSourceFunctional g hg F v =
      radiusTwoMetricSourceFunctional g hg F (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))) :
    v = radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) := by
  let J : RadiusTwoH1Zero → ℝ := radiusTwoMetricSourceFunctional g hg F
  let C : RadiusTwoH1Zero → ℝ := coerciveSourceFunctional
    (radiusTwoMetricEnergyL0Normalized g hg)
    (TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F))
  let w : RadiusTwoH1Zero := radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)
  have hJC : ∀ z, J z = C z := fun z =>
    radiusTwoMetricSourceFunctional_eq_normalizedEnergy g hg F z
  have hEq : C v = C w := scalarFunction_eq_of_pointwise_eq J C hJC hEqual
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "UNIQUE FUNCTION ALIAS TRANSPORT COMPLETE"
    out.flush
  exact eq_of_radiusTwoCoerciveSourceFunctional_eq_min
    (radiusTwoMetricEnergyL0Normalized g hg)
    (TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F))
    (isCoercive_radiusTwoMetricEnergyL0Normalized g hg)
    (radiusTwoMetricEnergyL0Normalized_comm g hg)
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))
    (radiusTwoMetricEnergyL0Normalized_source_equation g hg F) v hEq

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eq_radiusTwoSourceSolution_of_functional_eq
