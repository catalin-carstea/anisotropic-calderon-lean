import Calderon.SourceResponseEuclideanChart
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily MetricVolume

theorem fderiv_radiusTwoSmoothSourceResponse_sum_smul
    {ι : Type*} [Fintype ι]
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (s : ι → 𝓓(fixedExteriorSourceOpens, ℝ)) (a : ι → ℝ)
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg
      (∑ j, a j • s j)) x =
      ∑ j, a j • fderiv ℝ
        (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (s j)) x := by
  classical
  let L : 𝓓(fixedExteriorSourceOpens, ℝ) →ₗ[ℝ] (R3 →L[ℝ] ℝ) :=
    { toFun := fun f => fderiv ℝ
        (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg f) x
      map_add' := fun f h => radiusTwoSmoothSourceResponse_fderiv_add
        fixedDirichletRegularity fixedSobolevCalculus g hg f h x hx
      map_smul' := fun c f => radiusTwoSmoothSourceResponse_fderiv_smul
        fixedDirichletRegularity fixedSobolevCalculus g hg c f x hx }
  change L (∑ j, a j • s j) = ∑ j, a j • L (s j)
  simp only [map_sum, map_smul]

theorem radiusTwoSourceEuclideanCoordinates_eq_sum_smul
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ)) :
    radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f =
      fun x => ∑ i : Fin 3,
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f i) x •
          coordinateVector i := by
  funext x
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  funext k
  change radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f k) x =
    (∑ i : Fin 3,
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg (f i) x •
        coordinateVector i) k
  fin_cases k <;> simp [Fin.sum_univ_three, coordinateVector, PiLp.single_apply]

theorem hasFDerivAt_radiusTwoSourceEuclideanCoordinates_sum_smulRight
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (x : R3) (hx : x ∈ (radiusTwoOpens : Set R3)) :
    HasFDerivAt
      (radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f)
      (∑ i : Fin 3,
        (fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
          g hg (f i)) x).smulRight (coordinateVector i)) x := by
  rw [radiusTwoSourceEuclideanCoordinates_eq_sum_smul]
  exact HasFDerivAt.fun_sum fun i _ =>
    (differentiableAt_radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
      g hg (f i) x hx).hasFDerivAt.smul_const (coordinateVector i)

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
