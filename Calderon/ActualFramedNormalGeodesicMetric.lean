import Calderon.ActualNormalGeodesicMetric
import Calderon.FramedNormalizedEndpoint

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
open NormalCoordinatesFrame

theorem exists_actual_framed_normal_geodesic_metric
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v) (y0 : R3) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (A : Set (R3 × R3)),
      IsOpen A ∧ (y0,0) ∈ A ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ y, (y,0) ∈ A → ∀ t, Φ (y,0) t = (y,0)) ∧
      (∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ z) (geodesicPhaseField Q M (Φ z t)) t) ∧
      ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      (∀ y, (y,0) ∈ A → HasFDerivAt (fun z => (Φ z 1).1)
        (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) ∧
      (∀ y, (y,0) ∈ A → ∀ z u : R3,
        fderiv ℝ (fderiv ℝ (fun q => (Φ q 1).1)) (y,0) (0,z) (0,u) =
          -coordinateConnectionField Q M y z u) ∧
      (∀ y, (y,0) ∈ A → ∀ z : R3,
        normalizedEndpointMetric (fun q => (Φ q 1).1) M ((y,0),z) = M y ∧
        HasDerivAt (fun r : ℝ => normalizedEndpointMetric
          (fun q => (Φ q 1).1) M ((y,r),z)) 0 0) ∧
      ContDiff ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) ∧
      (∀ y, Function.Bijective (frameOperator (metricGramFrame (M y)))) ∧
      ContDiff ℝ ∞ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
        (fun y => frameOperator (metricGramFrame (M y)))) ∧
      ∀ y, (y,0) ∈ A → ∀ z : R3,
        framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,0),z) =
            ContinuousLinearMap.id ℝ R3 ∧
        HasDerivAt (fun r : ℝ => framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z)) 0 0 := by
  obtain ⟨Φ,A,hA,hy0,hΦ,h0,hstat,hODE,hΘ,hD,hH,hjet⟩ :=
    exists_smooth_coordinate_metric_endpoint_zero_radial_derivative Q M hQ hM hsym hMQ y0
  have hframe (y : R3) : IsMetricOrthonormalFrame (M y) (metricGramFrame (M y)) :=
    metricGramFrame_isMetricOrthonormalFrame (M y) (hsym y) (hpos y)
  have hF : ContDiff ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) :=
    contDiff_metricGramFrameOperator M hM hpos
  refine ⟨Φ,A,hA,hy0,hΦ,h0,hstat,hODE,hΘ,hD,hH,hjet,hF,
    (fun y => frameOperator_bijective (M y) _ (hframe y)),
    contDiff_framedNormalizedEndpointMetric _ M _ hΘ hM hF,?_⟩
  intro y hy z
  refine ⟨framedNormalizedEndpointMetric_zero _ M (fun x => metricGramFrame (M x)) y z
    (congrArg Prod.fst (hstat y hy 1)) (hD y hy) (hframe y),?_⟩
  exact hasDerivAt_framedNormalizedEndpointMetric_zero _ M _ y z
    (hjet y hy (frameOperator (metricGramFrame (M y)) z)).2
end OAI.AnisotropicCalderon.ConnectionError
