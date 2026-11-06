import Calderon.CollaboratorDirectSourceTwoJetsOct17
import Calderon.CollaboratorUniqueContinuationProofOct17
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceWitnesses
open EnergyBridge DirichletFamily Literature

theorem exists_radiusTwoSmoothSource_unitValue_zeroDerivatives
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg f p = 1 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg f) p = 0 ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg f)) p = 0 := by
  apply exists_radiusTwoSmoothSource_prescribed_twoJet_of_uniqueContinuation
    uniqueContinuation fixedDirichletRegularity fixedSobolevCalculus g hg p hp hSource 1 0 0
  · intro v w
    rfl
  · simp only [nativeMetricJetFunctional, ContinuousLinearMap.zero_apply, mul_zero,
      add_zero, Finset.sum_const_zero, neg_zero]

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceWitnesses
