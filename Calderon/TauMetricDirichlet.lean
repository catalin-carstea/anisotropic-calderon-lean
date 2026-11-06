import Calderon.TauAffineBall
import Calderon.TauMetricCoercivity

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual weak harmonic minimizers for the exact frozen smooth energy data. -/
theorem exists_affineDirichletSolution_of_admissible
    (hzero : SmoothBoundaryZeroClosure) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : SmoothData) :
    ∃ U : BallH1,
      U - smoothSobolev f ∈ TauCeti.w1p0Submodule volume ballOpens 2 ∧
      (∀ v : BallH1Zero, TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 U
        (v : BallH1) = 0) ∧
      minimalEnergy g f.1 = TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 U U := by
  let hc := memLp_metricEnergyIntegrand g hg
  let hco := isCoercive_metricEnergyForm g hg
  refine ⟨affineDirichletSolution g f hc hco, ?_, ?_, ?_⟩
  · have he : affineDirichletSolution g f hc hco - smoothSobolev f =
        (affineDirichletCorrection g f hc hco : BallH1) := by
      change smoothSobolev f + (affineDirichletCorrection g f hc hco : BallH1) -
        smoothSobolev f = _
      abel
    rw [he]
    exact (affineDirichletCorrection g f hc hco).2
  · exact energyForm_affineDirichletSolution_zero g f hc hco
  · exact minimalEnergy_eq_affineDirichletSolution_energy hzero g f hc hco
      (metricEnergy_coefficient_isSymm_ae g hg)

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.exists_affineDirichletSolution_of_admissible
