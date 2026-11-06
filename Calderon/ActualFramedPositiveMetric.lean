import Calderon.ActualUniformFramedEllipticity
import Calderon.PositiveMatrixExtension
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError NormalCoordinatesFrame

def framedNormalizedEndpointMetricMatrix (Theta : R3 × R3 → R3) (M F : R3 → R3 →L[ℝ] R3)
    (p : (R3 × ℝ) × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  operatorMatrixMap (framedNormalizedEndpointMetric Theta M F p)

theorem contDiff_framedNormalizedEndpointMetricMatrix (Theta : R3 × R3 → R3)
    (M F : R3 → R3 →L[ℝ] R3) (hG : ContDiff ℝ ∞ (framedNormalizedEndpointMetric Theta M F)) :
    ContDiff ℝ ∞ (framedNormalizedEndpointMetricMatrix Theta M F) :=
  operatorMatrixMap.contDiff.comp hG

theorem framedNormalizedEndpointMetric_symmetric (Theta : R3 × R3 → R3)
    (M F : R3 → R3 →L[ℝ] R3)
    (hsym : ∀ x u v, inner ℝ (M x u) v = inner ℝ (M x v) u)
    (p : (R3 × ℝ) × R3) (u v : R3) :
    inner ℝ (framedNormalizedEndpointMetric Theta M F p u) v =
      inner ℝ (framedNormalizedEndpointMetric Theta M F p v) u := by
  rw [framedNormalizedEndpointMetric_inner,framedNormalizedEndpointMetric_inner]
  exact hsym _ _ _

theorem operatorMatrixMap_id : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = 1 := by
  change matrixOperatorAlgEquiv.symm (1 : R3 →L[ℝ] R3) = 1
  exact map_one matrixOperatorAlgEquiv.symm

theorem exists_actual_framed_positive_metric
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v)
    (y0 : R3) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε B : ℝ)
      (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ),
      0 < ε ∧ 0 ≤ B ∧
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
      ContDiff ℝ ∞ H ∧ (∀ p, (H p).PosDef) ∧
      (∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
        H p = framedNormalizedEndpointMetricMatrix (fun q => (Φ q 1).1) M
          (fun x => frameOperator (metricGramFrame (M x))) p) ∧
      (∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → H ((y,0),z) = 1) ∧
      ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
        HasDerivAt (fun r : ℝ => H ((y,r),z)) 0 0 := by
  obtain ⟨Phi,epsilon,B,he,hB,hPhi,h0,hTheta,hF,hbij,hG,hdata⟩ :=
    exists_actual_uniform_framed_ellipticity Q M hQ hM hsym hMQ hpos y0
      (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
  let F := fun x => frameOperator (metricGramFrame (M x))
  let Theta : R3 × R3 → R3 := fun q => (Phi q 1).1
  let G := framedNormalizedEndpointMetricMatrix Theta M F
  have hb (p : (R3 × ℝ) × R3) (hp : dist p.1 (y0,0) ≤ epsilon) :
      ‖p.1.1-y0‖ ≤ epsilon ∧ |p.1.2| ≤ epsilon := by
    rw [dist_eq_norm] at hp
    change max ‖p.1.1-y0‖ ‖p.1.2-(0 : ℝ)‖ ≤ epsilon at hp
    simpa only [sub_zero,Real.norm_eq_abs] using max_le_iff.mp hp
  have hGP (p : (R3 × ℝ) × R3) (hp : dist p.1 (y0,0) ≤ epsilon)
      (hz : ‖p.2‖ ≤ 2) : (G p).PosDef := by
    obtain ⟨hy,hr⟩ := hb p hp
    have hk : p.2 ∈ closedBall (0 : R3) 2 := by
      simpa only [mem_closedBall,dist_zero_right] using hz
    have hlower := (hdata p.1.1 hy p.1.2 hr p.2 hk).2.2.2.2.2.1
    apply operatorMatrixMap_posDef (framedNormalizedEndpointMetric Theta M F p)
      (framedNormalizedEndpointMetric_symmetric Theta M F hsym p)
    intro u hu
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    exact lt_of_lt_of_le (mul_pos (by norm_num) (sq_pos_of_pos hn)) (hlower u)
  let H := positiveMatrixExtension G 1 (y0,0) epsilon 2 he (by norm_num)
  have hHs : ContDiff ℝ ∞ H := contDiff_positiveMatrixExtension G
    (contDiff_framedNormalizedEndpointMetricMatrix Theta M F hG)
    1 (y0,0) epsilon 2 he (by norm_num)
  have hHP (p : (R3 × ℝ) × R3) : (H p).PosDef :=
    positiveMatrixExtension_posDef G 1 Matrix.PosDef.one (y0,0) epsilon 2 he
      (by norm_num) hGP p
  refine ⟨Phi,epsilon,B,H,he,hB,hPhi,h0,hTheta,hF,hbij,hG,hdata,hHs,hHP,?_,?_,?_⟩
  · intro p hp hz
    exact positiveMatrixExtension_eq_on_inner G 1 (y0,0) epsilon 2 he (by norm_num) p hp hz
  · intro y hy z hz
    have hp : dist (y,(0 : ℝ)) (y0,0) ≤ epsilon/4 := by
      rw [dist_eq_norm]
      simpa using hy
    rw [show H ((y,0),z) = G ((y,0),z) from
      positiveMatrixExtension_eq_on_inner G 1 (y0,0) epsilon 2 he (by norm_num) ((y,0),z) hp hz]
    have hzero := (hdata y (hy.trans (by linarith)) 0 (by simpa using he.le) z
      (by simpa only [mem_closedBall,dist_zero_right] using hz.trans (by norm_num : (1 : ℝ) ≤ 2))).2.1
    change operatorMatrixMap (framedNormalizedEndpointMetric Theta M F ((y,0),z)) = 1
    rw [hzero,operatorMatrixMap_id]
  · intro y hy z hz
    have hk : z ∈ closedBall (0 : R3) 2 := by
      simpa only [mem_closedBall,dist_zero_right] using hz.trans (by norm_num : (1 : ℝ) ≤ 2)
    have hj := (hdata y (hy.trans (by linarith)) 0 (by simpa using he.le) z hk).2.2.1
    have hd := operatorMatrixMap.hasFDerivAt.comp_hasDerivAt 0 hj
    change HasDerivAt (fun r : ℝ => G ((y,r),z)) 0 0 at hd
    have heq : (fun r : ℝ => H ((y,r),z)) =ᶠ[𝓝 (0 : ℝ)] (fun r => G ((y,r),z)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < epsilon/8)] with r hr
      have hr' : |r| < epsilon/8 := by
        simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hr
      have hp : dist (y,r) (y0,(0 : ℝ)) ≤ epsilon/4 := by
        rw [dist_eq_norm]
        change max ‖y-y0‖ ‖r-(0 : ℝ)‖ ≤ epsilon/4
        apply max_le
        · linarith
        · simpa only [sub_zero,Real.norm_eq_abs] using (by linarith : |r| ≤ epsilon/4)
      exact positiveMatrixExtension_eq_on_inner G 1 (y0,0) epsilon 2 he (by norm_num) ((y,r),z) hp hz
    exact hd.congr_of_eventuallyEq heq
end OAI.AnisotropicCalderon.MetricOperator
