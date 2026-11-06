import Calderon.GeodesicEndpointSecondJet
import Calderon.NormalMetricOperatorFirstJet
import Calderon.CoordinateMetricCompatibility
import Calderon.MetricOperator

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

theorem exists_smooth_coordinate_metric_endpoint_zero_radial_derivative
    (Q M : E → E →L[ℝ] E) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V) (y0 : E) :
    ∃ (Φ : (E × E) → ℝ → E × E) (A : Set (E × E)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (E × E) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ y, (y,0) ∈ A → ∀ t, Φ (y,0) t = (y,0)) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField Q M (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      (∀ y, (y,0) ∈ A → HasFDerivAt (fun z => (Φ z 1).1)
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (y,0)) ∧
      (∀ y, (y,0) ∈ A → ∀ z u : E,
        fderiv ℝ (fderiv ℝ (fun q => (Φ q 1).1)) (y,0) (0,z) (0,u) =
          -coordinateConnectionField Q M y z u) ∧
      ∀ y, (y,0) ∈ A → ∀ z : E,
        normalizedEndpointMetric (fun q => (Φ q 1).1) M ((y,0),z) = M y ∧
        HasDerivAt (fun r : ℝ => normalizedEndpointMetric
          (fun q => (Φ q 1).1) M ((y,r),z)) 0 0 := by
  obtain ⟨Φ,A,hA,hy0,hF,h0,hstat,hODE,hΘ,hD,hH⟩ :=
    exists_smooth_coordinate_spray_endpoint_secondJet Q M hQ hM y0
  have hHH (y : E) (hy : (y,0) ∈ A) (z u : E) :
      fderiv ℝ (fderiv ℝ (fun q => (Φ q 1).1)) (y,0) (0,z) (0,u) =
        -coordinateConnectionField Q M y z u := by
    rw [hH y hy (0,u) (0,z)]
    rw [coordinateConnectionField_symmetric_of_metric Q M hM hsym y u z]
    rw [show coordinateConnectionField Q M y z u + coordinateConnectionField Q M y z u =
      (2 : ℝ) • coordinateConnectionField Q M y z u by simp [two_smul]]
    rw [smul_smul]
    norm_num
  refine ⟨Φ,A,hA,hy0,hF,h0,hstat,hODE,hΘ,hD,hHH,?_⟩
  intro y hy z
  have hzero : (Φ (y,0) 1).1 = y := congrArg Prod.fst (hstat y hy 1)
  exact ⟨normalizedEndpointMetric_zero _ M y z hzero (hD y hy),
    hasDerivAt_normalizedEndpointMetric_zero _ M hΘ hM y z
      (coordinateConnectionField Q M y) hzero (hD y hy) (hHH y hy)
      (coordinateConnectionField_metric_compatible Q M hM hsym hMQ y)⟩
end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError
theorem exists_actual_normal_geodesic_metric (g : MatrixField) (hg : IsAdmissibleMetric g)
    (y0 : R3) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (A : Set (R3 × R3)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (Φ z)
        (geodesicPhaseField (inverseMetricField (metricOperatorField g))
          (metricOperatorField g) (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ∀ y, (y,0) ∈ A → ∀ z : R3,
        normalizedEndpointMetric (fun q => (Φ q 1).1) (metricOperatorField g) ((y,0),z) =
          metricOperatorField g y ∧
        HasDerivAt (fun r : ℝ => normalizedEndpointMetric
          (fun q => (Φ q 1).1) (metricOperatorField g) ((y,r),z)) 0 0 := by
  obtain ⟨Φ,A,hA,hy0,hF,h0,_,hODE,hΘ,_,_,hjet⟩ :=
    exists_smooth_coordinate_metric_endpoint_zero_radial_derivative
      (inverseMetricField (metricOperatorField g)) (metricOperatorField g)
      (contDiff_inverseMetricField _ (contDiff_metricOperatorField g hg)
        (isUnit_metricOperatorField g hg)) (contDiff_metricOperatorField g hg)
      (metricOperatorField_symmetric g hg)
      (metric_apply_inverseMetricField _ (isUnit_metricOperatorField g hg)) y0
  exact ⟨Φ,A,hA,hy0,hF,h0,hODE,hΘ,hjet⟩
end OAI.AnisotropicCalderon.MetricOperator
