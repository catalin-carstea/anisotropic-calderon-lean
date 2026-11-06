import Calderon.ActualUniformFramedNormalMetric
import Calderon.NearIdentityEllipticity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
open NormalCoordinatesFrame

theorem exists_actual_uniform_framed_ellipticity
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v)
    (y0 : R3) (K : Set R3) (hK : IsCompact K) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε B : ℝ),
      0 < ε ∧ 0 ≤ B ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧ ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ContDiff ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) ∧
      (∀ y, Function.Bijective (frameOperator (metricGramFrame (M y)))) ∧
      ContDiff ℝ ∞ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
        (fun y => frameOperator (metricGramFrame (M y)))) ∧
      ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ K,
        (∀ t ∈ Icc (0 : ℝ) 1,
          HasDerivAt (Φ (y,r • frameOperator (metricGramFrame (M y)) z))
            (geodesicPhaseField Q M (Φ (y,r • frameOperator (metricGramFrame (M y)) z) t)) t) ∧
        framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,0),z) =
            ContinuousLinearMap.id ℝ R3 ∧
        HasDerivAt (fun r : ℝ => framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z)) 0 0 ∧
        ‖framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z) -
            ContinuousLinearMap.id ℝ R3‖ ≤ B*r^2 ∧
        ‖framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z) -
            ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ) ∧
        (∀ u : R3, (1/2 : ℝ)*‖u‖^2 ≤
          inner ℝ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
            (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z) u) u) ∧
        ∀ u v : R3, |inner ℝ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
            (fun x => frameOperator (metricGramFrame (M x))) ((y,r),z) u) v| ≤
              (3/2 : ℝ)*‖u‖*‖v‖ := by
  obtain ⟨Φ,epsilon,B,he,hB,hPhi,h0,hTheta,hF,hbij,hG,hdata⟩ :=
    exists_actual_uniform_framed_normal_metric Q M hQ hM hsym hMQ hpos y0 K hK
  obtain ⟨delta,hd,hde,hsmall⟩ := exists_common_radius_quadratic_le_half epsilon B he hB
  refine ⟨Φ,delta,B,hd,hB,hPhi,h0,hTheta,hF,hbij,hG,?_⟩
  intro y hy r hr z hz
  have h := hdata y (hy.trans hde) r (hr.trans hde) z hz
  have hh := h.2.2.2.trans (hsmall r hr)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hh,
    inner_lower_bound_of_norm_sub_id_le_half _ hh,
    inner_upper_bound_of_norm_sub_id_le_half _ hh⟩
end OAI.AnisotropicCalderon.ConnectionError
