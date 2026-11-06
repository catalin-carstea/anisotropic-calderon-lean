import Calderon.ActualFramedPositiveMetric
import Calderon.WeightedCommonSupportCoefficients
import Calderon.PositiveMatrixPointCalculus
import Calderon.NormalizedConformalDrift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError NormalCoordinatesFrame

theorem exists_actual_framed_coefficients_drift
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v)
    (y0 : R3) (L : ℝ) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε B : ℝ)
      (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (R3 × ℝ) × R3 → ℝ),
      (0 < ε ∧ 0 ≤ B ∧
      ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧ ContDiff ℝ ∞ (fun z => (Φ z 1).1) ∧
      ContDiff ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) ∧
      (∀ y, Function.Bijective (frameOperator (metricGramFrame (M y)))) ∧
      ContDiff ℝ ∞ (framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M
        (fun y => frameOperator (metricGramFrame (M y)))) ∧
      (∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε → ∀ z ∈ closedBall (0 : R3) 2,
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
              (3/2 : ℝ)*‖u‖*‖v‖ ) ∧
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ w ∧
      (∀ p : R3 × ℝ, ∀ z : R3, z ∉ closedBall (0 : R3) 3 → a (p,z)=0 ∧ w (p,z)=0) ∧
      (∃ lam Lam : ℝ, ∀ p ∈ closedBall (y0,(0 : ℝ)) (ε/4),
        TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1) (fun z => a (p,z)) lam Lam) ∧
      (∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
        a p = matrixPrincipalCoefficient
          (framedNormalizedEndpointMetricMatrix (fun q => (Φ q 1).1) M
            (fun x => frameOperator (metricGramFrame (M x)))) p ∧
        w p = matrixVolumeDensity
          (framedNormalizedEndpointMetricMatrix (fun q => (Φ q 1).1) M
            (fun x => frameOperator (metricGramFrame (M x)))) p) ∧
      (∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → a ((y,0),z)=1 ∧ w ((y,0),z)=1) ∧
      ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
        HasDerivAt (fun r : ℝ => a ((y,r),z)) 0 0 ∧
        HasDerivAt (fun r : ℝ => w ((y,r),z)) 0 0) ∧
      (ContDiff ℝ ∞ H ∧ (∀ p, (H p).PosDef) ∧
      (∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
        H p = framedNormalizedEndpointMetricMatrix (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) p) ∧
      (∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → H ((y,0),z) = 1) ∧
      ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
        HasDerivAt (fun r : ℝ => H ((y,r),z)) 0 0) ∧
      a = cutoffPrincipalCoefficient H ∧ w = cutoffVolumeDensity H ∧
      ContDiff ℝ ∞ (normalizedConformalDriftBase H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y)))) ∧
      ContDiff ℝ ∞ (normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L) ∧
      (∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
        framedNormalizedEndpointMetric (fun q => (Φ q 1).1) M (fun y => frameOperator (metricGramFrame (M y))) p (normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L p) =
          (-L*p.1.2) • ((framedNormalizedEndpointDerivative (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) p).adjoint (gradient conformalReferenceCoordinateDepth (framedScaledEndpoint (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) p)))) ∧
      (∀ y z : R3, normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L ((y,0),z) = 0) ∧
      (∀ y z : R3, HasDerivAt (fun r : ℝ => normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L ((y,r),z))
        (-L • normalizedConformalDriftBase H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) ((y,0),z)) 0) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        (∀ j : ℕ, j ≤ N → ∀ p ∈ (closedBall (y0,(0 : ℝ)) (ε/4)) ×ˢ (closedBall (0 : R3) 1),
          ‖iteratedFDeriv ℝ j (normalizedConformalDriftBase H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y)))) p‖ ≤ C) ∧
        ∀ p ∈ (closedBall (y0,(0 : ℝ)) (ε/4)) ×ˢ (closedBall (0 : R3) 1),
          ‖normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L p‖ ≤ |L| * C * |p.1.2| := by
  obtain ⟨Phi,epsilon,B,H,he,hB,hPhi,h0,hTheta,hF,hbij,hG,hdata,hHs,hpos,hloc,hzero,hjet⟩ :=
    exists_actual_framed_positive_metric Q M hQ hM hsym hMQ hpos y0
  let a := cutoffPrincipalCoefficient H
  let w := cutoffVolumeDensity H
  have ha : ContDiff ℝ ∞ a := contDiff_cutoffPrincipalCoefficient H hHs hpos
  have hw : ContDiff ℝ ∞ w := contDiff_cutoffVolumeDensity H hHs hpos
  obtain ⟨lam,Lam,hUE⟩ := exists_uniformlyElliptic_cutoffPrincipalCoefficient H hHs hpos
    (closedBall (y0,(0 : ℝ)) (epsilon/4)) (isCompact_closedBall _ _)
  let Theta : R3 × R3 → R3 := fun q => (Phi q 1).1
  let F : R3 → R3 →L[ℝ] R3 := fun y => frameOperator (metricGramFrame (M y))
  refine ⟨Phi,epsilon,B,H,a,w,?_,⟨hHs,hpos,hloc,hzero,hjet⟩,rfl,rfl,
    contDiff_normalizedConformalDriftBase H hHs hpos Theta hTheta F hF,
    contDiff_normalizedConformalDrift H hHs hpos Theta hTheta F hF L,?_,?_,?_,?_⟩
  ·
    refine ⟨he,hB,hPhi,h0,hTheta,hF,hbij,hG,hdata,ha,hw,?_,⟨lam,Lam,hUE⟩,?_,?_,?_⟩
    · intro p z hz
      have hn : 3 ≤ ‖z‖ := le_of_lt (lt_of_not_ge (by
        simpa only [mem_closedBall,dist_zero_right] using hz))
      exact ⟨cutoffPrincipalCoefficient_eq_zero_outside H (p,z) hn,
        cutoffVolumeDensity_eq_zero_outside H (p,z) hn⟩
    · intro p hp hz
      have heq := hloc p hp hz
      constructor
      · rw [show a p = matrixPrincipalCoefficient H p from cutoffPrincipalCoefficient_eq_on_unitBall H p hz]
        simp only [matrixPrincipalCoefficient,matrixVolumeDensity,heq]
      · rw [show w p = matrixVolumeDensity H p from cutoffVolumeDensity_eq_on_unitBall H p hz]
        simp only [matrixVolumeDensity,heq]
    · intro y hy z hz
      have heq := hzero y hy z hz
      constructor
      · rw [show a ((y,0),z) = matrixPrincipalCoefficient H ((y,0),z) from
          cutoffPrincipalCoefficient_eq_on_unitBall H ((y,0),z) hz]
        simp [matrixPrincipalCoefficient,matrixVolumeDensity,heq]
      · rw [show w ((y,0),z) = matrixVolumeDensity H ((y,0),z) from
          cutoffVolumeDensity_eq_on_unitBall H ((y,0),z) hz]
        simp [matrixVolumeDensity,heq]
    · intro y hy z hz
      have hj := hjet y hy z hz
      have hja := hasDerivAt_matrixPrincipalCoefficient_zero
        (fun r : ℝ => H ((y,r),z)) 0 hj (hpos ((y,0),z))
      have hjw := hasDerivAt_matrixVolumeDensity_zero
        (fun r : ℝ => H ((y,r),z)) 0 hj (hpos ((y,0),z))
      have hea : (fun r : ℝ => a ((y,r),z)) = matrixPrincipalCoefficient (fun r : ℝ => H ((y,r),z)) := by
        funext r
        exact cutoffPrincipalCoefficient_eq_on_unitBall H ((y,r),z) hz
      have hew : (fun r : ℝ => w ((y,r),z)) = matrixVolumeDensity (fun r : ℝ => H ((y,r),z)) := by
        funext r
        exact cutoffVolumeDensity_eq_on_unitBall H ((y,r),z) hz
      constructor
      · rw [hea]; exact hja
      · rw [hew]; exact hjw
  · intro p hp hz
    exact normalizedConformalDrift_local_metric_identity H hpos Theta M F L p (hloc p hp hz)
  · intro y z
    exact normalizedConformalDrift_zero H Theta F L y z
  · intro y z
    exact hasDerivAt_normalizedConformalDrift_zero H hHs hpos Theta hTheta F hF L y z
  · intro N
    exact exists_compact_normalizedConformalDrift_bounds H hHs hpos Theta hTheta F hF L
      ((closedBall (y0,(0 : ℝ)) (epsilon/4)) ×ˢ (closedBall (0 : R3) 1))
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) N
end OAI.AnisotropicCalderon.MetricOperator
