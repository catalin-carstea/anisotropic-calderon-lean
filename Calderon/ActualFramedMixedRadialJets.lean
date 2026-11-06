import Calderon.MixedRadialJetCalculus
import Calderon.ActualFramedCoefficientsDrift
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Constructions.SumProd

/-! The signed radius room epsilon/16 is chosen
    before any jet order, and the spatial compact is the full closed unit ball. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped Topology ContDiff Gradient Matrix.Norms.Elementwise

namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError NormalCoordinatesFrame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reassociate the literal center, radius and spatial coefficient variables. -/
def centerSpatialRadius (F : (R3 × ℝ) × R3 → V) : (R3 × R3) × ℝ → V :=
  fun p => F ((p.1.1,p.2),p.1.2)

theorem contDiff_centerSpatialRadius (F : (R3 × ℝ) × R3 → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (centerSpatialRadius F) :=
  hF.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)

/-- Actual joint center/spatial jets, with no radial slot. -/
def coefficientMixedJet (j : ℕ) (F : (R3 × ℝ) × R3 → V) :=
  parameterJetField j (centerSpatialRadius F)

theorem coefficientMixedJet_eq_iteratedFDeriv (j : ℕ)
    (F : (R3 × ℝ) × R3 → V) (hF : ContDiff ℝ ∞ F) (y z : R3) (r : ℝ) :
    coefficientMixedJet j F ((y,z),r) =
      iteratedFDeriv ℝ j (fun p : R3 × R3 => F ((p.1,r),p.2)) (y,z) :=
  parameterJetField_eq_iteratedFDeriv j (centerSpatialRadius F)
    (contDiff_centerSpatialRadius F hF) (y,z) r

/-- Preserve literal coefficient identities at all jet orders, including spatial boundary points. -/
theorem coefficientMixedJet_eq_of_eq_on_geometric_room
    (F G : (R3 × ℝ) × R3 → V) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (ε : ℝ) (hε : 0 < ε) (y0 : R3)
    (heq : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 → F p = G p)
    (j : ℕ) (y z : R3) (r : ℝ) (hy : ‖y-y0‖ ≤ ε/16) (hz : ‖z‖ ≤ 1)
    (hr : |r| ≤ ε/16) :
    coefficientMixedJet j F ((y,z),r) = coefficientMixedJet j G ((y,z),r) := by
  let s : Set (R3 × R3) := ball y0 (ε/8) ×ˢ ball (0 : R3) 1
  have hs : IsOpen s := isOpen_ball.prod isOpen_ball
  have hcl : closure s = closedBall y0 (ε/8) ×ˢ closedBall (0 : R3) 1 := by
    simp only [s, closure_prod_eq, closure_ball y0 (by positivity : ε/8 ≠ 0),
      closure_ball (0 : R3) (by norm_num : (1 : ℝ) ≠ 0)]
  have hlocal : ∀ p ∈ s, centerSpatialRadius F (p,r) = centerSpatialRadius G (p,r) := by
    intro p hp
    have hy' : ‖p.1-y0‖ < ε/8 := by simpa only [mem_ball,dist_eq_norm] using hp.1
    have hz' : ‖p.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hp.2
    have hd : dist (p.1,r) (y0,(0 : ℝ)) ≤ ε/4 := by
      rw [dist_eq_norm]
      change max ‖p.1-y0‖ ‖r-(0 : ℝ)‖ ≤ ε/4
      refine max_le (by linarith) ?_
      simpa only [sub_zero,Real.norm_eq_abs] using (by linarith : |r| ≤ ε/4)
    exact heq ((p.1,r),p.2) hd hz'.le
  have hp : (y,z) ∈ closure s := by
    rw [hcl]
    exact ⟨by simpa only [mem_closedBall,dist_eq_norm] using (by linarith : ‖y-y0‖ ≤ ε/8),
      by simpa only [mem_closedBall,dist_zero_right] using hz⟩
  exact parameterJetField_eq_on_closure j (centerSpatialRadius F) (centerSpatialRadius G)
    (contDiff_centerSpatialRadius F hF) (contDiff_centerSpatialRadius G hG) s hs r hlocal (y,z) hp

/-- Derive all finite mixed quadratic bounds from only the exported zeroth radial jets. -/
theorem exists_coefficientMixedJet_quadratic_bound
    (F : (R3 × ℝ) × R3 → V) (hF : ContDiff ℝ ∞ F) (y0 : R3)
    (ε : ℝ) (hε : 0 < ε)
    (hzero : ∀ y : R3, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → F ((y,0),z) = 0)
    (hjet : ∀ y : R3, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => F ((y,r),z)) 0 0) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N →
      ∀ y : R3, ‖y-y0‖ ≤ ε/16 → ∀ z : R3, ‖z‖ ≤ 1 →
      ∀ r : ℝ, |r| ≤ ε/16 → ‖coefficientMixedJet j F ((y,z),r)‖ ≤ C * r^2 := by
  let s : Set (R3 × R3) := ball y0 (ε/8) ×ˢ ball (0 : R3) 1
  let q : Set (R3 × R3) := closedBall y0 (ε/16) ×ˢ closedBall (0 : R3) 1
  have hs : IsOpen s := isOpen_ball.prod isOpen_ball
  have hq : IsCompact q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hc : closure s = closedBall y0 (ε/8) ×ˢ closedBall (0 : R3) 1 := by
    simp only [s, closure_prod_eq, closure_ball y0 (by positivity : ε/8 ≠ 0),
      closure_ball (0 : R3) (by norm_num : (1 : ℝ) ≠ 0)]
  have hqs : q ⊆ closure s := by
    intro p hp
    rw [hc]
    refine ⟨?_,hp.2⟩
    exact closedBall_subset_closedBall (by linarith : ε/16 ≤ ε/8) hp.1
  have hz : ∀ p ∈ s, centerSpatialRadius F (p,0) = 0 := by
    intro p hp
    have hy : ‖p.1-y0‖ < ε/8 := by simpa only [mem_ball,dist_eq_norm] using hp.1
    have hx : ‖p.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hp.2
    exact hzero p.1 (by linarith) p.2 hx.le
  have hj : ∀ p ∈ s, HasDerivAt (fun r : ℝ => centerSpatialRadius F (p,r)) 0 0 := by
    intro p hp
    have hy : ‖p.1-y0‖ < ε/8 := by simpa only [mem_ball,dist_eq_norm] using hp.1
    have hx : ‖p.2‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hp.2
    exact hjet p.1 hy.le p.2 hx.le
  intro N
  obtain ⟨C,hC,hbound⟩ := exists_compact_uniform_parameterJet_quadratic_bound
    (centerSpatialRadius F) (contDiff_centerSpatialRadius F hF) s q hs hq hqs hz hj
    (ε/16) (by positivity) N
  refine ⟨C,hC,?_⟩
  intro j hj y hy z hz r hr
  have hp : (y,z) ∈ q := by
    exact ⟨by simpa only [mem_closedBall,dist_eq_norm] using hy,
      by simpa only [mem_closedBall,dist_zero_right] using hz⟩
  exact hbound j hj (y,z) hp r hr

/-- All three coefficient errors are bounded on the same signed room. -/
def ActualCoefficientMixedJetBounds
    (ε : ℝ) (y0 : R3)
    (H a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (R3 × ℝ) × R3 → ℝ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, j ≤ N →
    ∀ y : R3, ‖y-y0‖ ≤ ε/16 → ∀ z : R3, ‖z‖ ≤ 1 →
    ∀ r : ℝ, |r| ≤ ε/16 →
      ‖coefficientMixedJet j (fun p => H p - 1) ((y,z),r)‖ ≤ C*r^2 ∧
      ‖coefficientMixedJet j (fun p => a p - 1) ((y,z),r)‖ ≤ C*r^2 ∧
      ‖coefficientMixedJet j (fun p => w p - 1) ((y,z),r)‖ ≤ C*r^2

theorem actualCoefficientMixedJetBounds_of_zero_radial_jets
    (ε : ℝ) (y0 : R3) (hε : 0 < ε)
    (H a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (R3 × ℝ) × R3 → ℝ)
    (hH : ContDiff ℝ ∞ H) (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hzeroH : ∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → H ((y,0),z)=1)
    (hzero : ∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 →
      a ((y,0),z)=1 ∧ w ((y,0),z)=1)
    (hjetH : ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => H ((y,r),z)) 0 0)
    (hjet : ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => a ((y,r),z)) 0 0 ∧
      HasDerivAt (fun r : ℝ => w ((y,r),z)) 0 0) :
    ActualCoefficientMixedJetBounds ε y0 H a w := by
  have hzH : ∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → H ((y,0),z)-1=0 := by
    intro y hy z hz
    rw [hzeroH y hy z hz,sub_self]
  have hza : ∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → a ((y,0),z)-1=0 := by
    intro y hy z hz
    rw [(hzero y hy z hz).1,sub_self]
  have hzw : ∀ y, ‖y-y0‖ ≤ ε/4 → ∀ z : R3, ‖z‖ ≤ 1 → w ((y,0),z)-1=0 := by
    intro y hy z hz
    rw [(hzero y hy z hz).2,sub_self]
  have hjH : ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => H ((y,r),z)-1) 0 0 := by
    intro y hy z hz
    exact (hjetH y hy z hz).sub_const 1
  have hja : ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => a ((y,r),z)-1) 0 0 := by
    intro y hy z hz
    exact ((hjet y hy z hz).1).sub_const 1
  have hjw : ∀ y, ‖y-y0‖ ≤ ε/8 → ∀ z : R3, ‖z‖ ≤ 1 →
      HasDerivAt (fun r : ℝ => w ((y,r),z)-1) 0 0 := by
    intro y hy z hz
    exact ((hjet y hy z hz).2).sub_const 1
  intro N
  obtain ⟨CH,hCH,hbH⟩ := exists_coefficientMixedJet_quadratic_bound
    (fun p => H p - 1) (hH.sub contDiff_const) y0 ε hε hzH hjH N
  obtain ⟨Ca,hCa,hba⟩ := exists_coefficientMixedJet_quadratic_bound
    (fun p => a p - 1) (ha.sub contDiff_const) y0 ε hε hza hja N
  obtain ⟨Cw,hCw,hbw⟩ := exists_coefficientMixedJet_quadratic_bound
    (fun p => w p - 1) (hw.sub contDiff_const) y0 ε hε hzw hjw N
  refine ⟨CH+Ca+Cw,by positivity,?_⟩
  intro j hj y hy z hz r hr
  refine ⟨(hbH j hj y hy z hz r hr).trans ?_,
    (hba j hj y hy z hz r hr).trans ?_,(hbw j hj y hy z hz r hr).trans ?_⟩
  all_goals exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)

/-- Retain the ENTIRE original drift witness and conjoin the new mixed-jet bound. -/
theorem exists_actual_framed_coefficients_drift_with_mixed_radial_jets
    (Q M : R3 → R3 →L[ℝ] R3) (hQ : ContDiff ℝ ∞ Q) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V)
    (hpos : ∀ y v, v ≠ 0 → 0 < inner ℝ (M y v) v)
    (y0 : R3) (L : ℝ) :
    ∃ (Φ : (R3 × R3) → ℝ → R3 × R3) (ε B : ℝ)
      (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (R3 × ℝ) × R3 → ℝ),
      ((0 < ε ∧ 0 ≤ B ∧
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
          ‖normalizedConformalDrift H (fun q => (Φ q 1).1) (fun y => frameOperator (metricGramFrame (M y))) L p‖ ≤ |L| * C * |p.1.2|) ∧
      ActualCoefficientMixedJetBounds ε y0 H a w := by
  have hGeometry := exists_actual_framed_coefficients_drift Q M hQ hM hsym hMQ hpos y0 L
  cases hGeometry with
  | intro Phi hPhi =>
    cases hPhi with
    | intro epsilon hEpsilon =>
      cases hEpsilon with
      | intro B hB =>
        cases hB with
        | intro H hH =>
          cases hH with
          | intro a ha =>
            cases ha with
            | intro w hExisting =>
              have hCoeff := hExisting.1
              have hMetric := hExisting.2.1
              have hNew := actualCoefficientMixedJetBounds_of_zero_radial_jets
                epsilon y0 hCoeff.1 H a w hMetric.1 hCoeff.2.2.2.2.2.2.2.2.2.1 hCoeff.2.2.2.2.2.2.2.2.2.2.1 hMetric.2.2.2.1 hCoeff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hMetric.2.2.2.2 hCoeff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
              exact ⟨Phi,epsilon,B,H,a,w,hExisting,hNew⟩

end OAI.AnisotropicCalderon.MetricOperator
