import Calderon.RadiusTwoNativeFunctionalCorrespondence

/-! EXPANSION.json precedes this actual typed-energy min/unique specialization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoMetricSourceFunctional_min (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (v : RadiusTwoH1Zero) :
    radiusTwoMetricSourceFunctional g hg F (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) ≤
      radiusTwoMetricSourceFunctional g hg F v := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "TYPED MIN PROOF ENTER"
    out.flush
  have hMin := coerciveSourceFunctional_min (V := RadiusTwoH1Zero)
    (radiusTwoMetricEnergyL0Normalized g hg)
    (TauCeti.PDE.dirichletForcing (smoothRadiusTwoForcing F))
    (isCoercive_radiusTwoMetricEnergyL0Normalized g hg)
    (radiusTwoMetricEnergyL0Normalized_comm g hg)
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))
    (radiusTwoMetricEnergyL0Normalized_source_equation g hg F) v
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "TYPED MINIMUM COMPLETE"
    out.flush
  exact (radiusTwoMetricSourceFunctional_eq_normalizedEnergy g hg F
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))).le.trans
    (hMin.trans (radiusTwoMetricSourceFunctional_eq_normalizedEnergy g hg F v).symm.le)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "TYPED MIN BODY COMPLETE"
    out.flush

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricSourceFunctional_min
