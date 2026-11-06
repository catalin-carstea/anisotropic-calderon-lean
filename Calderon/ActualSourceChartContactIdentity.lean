import Calderon.ActualCanonicalSourceJetReconstruction
import Calderon.ActualSourceChartNativeFirstDerivative
import Calderon.NativeCoordinateOperatorAlgebra

set_option autoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators ContDiff Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge DirichletFamily

theorem radiusTwoSourceEuclideanCoordinates_inverse_columns_value
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ))
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
    (hDet : (radiusTwoSourceFreeJetMatrix g hg f p).det ≠ 0) :
    radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg
      (fun i : Fin 3 => ∑ j,
        ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j (Sum.inr (Sum.inl i)) • f j) p = 0 := by
  have hValue (i : Fin 3) :
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg
        (∑ j, ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j (Sum.inr (Sum.inl i)) • f j) p = 0 := by
    exact congrArg (fun J : RadiusTwoRawTwoJet => J.1)
      (radiusTwoSmoothSourceJet_inverse_column g hg p hp hSource f hDet (Sum.inr (Sum.inl i)))
  rw [radiusTwoSourceEuclideanCoordinates_eq_sum_smul]
  simp only [hValue, zero_smul, Finset.sum_const_zero]

theorem hasFDerivAt_radiusTwoSourceEuclideanCoordinates_inverse_columns_id
    (g : MatrixField) (hg : IsAdmissibleMetric g) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3))
    (hSource : p ∉ closedBall fixedExteriorSourceCenter (1/8 : ℝ))
    (f : (Fin 1 ⊕ (Fin 3 ⊕ Fin 5)) → 𝓓(fixedExteriorSourceOpens, ℝ))
    (hDet : (radiusTwoSourceFreeJetMatrix g hg f p).det ≠ 0) :
    HasFDerivAt
      (radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg
        (fun i : Fin 3 => ∑ j,
          ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j (Sum.inr (Sum.inl i)) • f j))
      (ContinuousLinearMap.id ℝ R3) p := by
  have hGradient (i : Fin 3) :
      fderiv ℝ (radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g hg
        (∑ j, ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j (Sum.inr (Sum.inl i)) • f j)) p =
          EuclideanSpace.proj i := by
    exact congrArg (fun J : RadiusTwoRawTwoJet => J.2.1)
      (radiusTwoSmoothSourceJet_inverse_column g hg p hp hSource f hDet (Sum.inr (Sum.inl i)))
  have h := hasFDerivAt_radiusTwoSourceEuclideanCoordinates_sum_smulRight g hg
    (fun i : Fin 3 => ∑ j,
      ((radiusTwoSourceFreeJetMatrix g hg f p)⁻¹) j (Sum.inr (Sum.inl i)) • f j) p hp
  simp only [hGradient, sum_projection_smulRight_coordinateVector] at h
  exact h

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
