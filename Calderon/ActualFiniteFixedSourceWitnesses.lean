import Calderon.ActualFiniteCompatibleSourceJetsFromUniqueContinuation
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceWitnesses
open EnergyBridge DirichletFamily Literature MetricCompatibleSourceJetAlgebra

theorem exists_radiusTwoSmoothSource_zeroGradient_fiveHessians
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : Fin 5 → 𝓓(fixedExteriorSourceOpens, ℝ), ∀ k : Fin 5,
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k) p = 0 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k)) p = 0 ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k))) p =
        matrixJetBilinear (traceFreeHessianMatrix ((g p)⁻¹) k) :=
  exists_radiusTwoSmoothSource_zeroGradient_fiveHessians_of_proved_uniqueContinuation
    fixedDirichletRegularity fixedSobolevCalculus g hg p hp hSource

theorem exists_radiusTwoSmoothSource_coordinate_firstJets
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ), ∀ k : Fin 3,
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k) p = 0 ∧
      fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k)) p =
        EuclideanSpace.proj k ∧
      fderiv ℝ (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k))) p =
        matrixJetBilinear
          (gradientCorrectionHessianMatrix g p (EuclideanSpace.proj k)) :=
  exists_radiusTwoSmoothSource_coordinate_firstJets_of_proved_uniqueContinuation
    fixedDirichletRegularity fixedSobolevCalculus g hg p hp hSource

theorem exists_radiusTwoSourceCoordinates_centered_localChart_of_twoJetRange
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ)) :
    ∃ (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
      (e : OpenPartialHomeomorph R3 (Fin 3 → ℝ)),
      (e : R3 → (Fin 3 → ℝ)) = radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f ∧
      e p = 0 ∧ p ∈ e.source ∧
      HasFDerivAt (radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f)
        (EuclideanSpace.equiv (Fin 3) ℝ : R3 →L[ℝ] (Fin 3 → ℝ)) p ∧
      ContDiffAt ℝ ∞ e.symm 0 :=
  exists_radiusTwoSourceCoordinates_centered_localChart_of_twoJetRange_of_proved_uniqueContinuation
    fixedDirichletRegularity fixedSobolevCalculus g hg p hp hSource

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceWitnesses
