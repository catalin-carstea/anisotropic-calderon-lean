import Calderon.CompactParameterReferenceGeodesicEndpointSecondJet
import Calderon.ParameterFramedNormalizedEndpoint
import Calderon.NormalMetricOperatorFirstJet
import Calderon.CoordinateMetricCompatibility
import Calderon.NearIdentityEllipticity

/-! UNCOMPILED author proposal. EXPANSION.md E4--E7 was sealed first.
One augmented-cutoff family is selected once, and all its original data are retained. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

private instance instCompleteJointFramedReferenceR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

/-- Transparent packaging of the entire strengthened original endpoint payload. -/
def ConformalReferenceGeodesicEndpointData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) : Prop :=
  IsOpen B ∧ (y0,0) ∈ B ∧
  ContDiff ℝ ∞ (fun p : (ℝ × (R3 × R3)) × ℝ => Φ p.1.1 p.1.2 p.2) ∧
  (∀ q z, Φ q z 0 = z) ∧
  (∀ q z t u, Φ q z (t+u) = Φ q (Φ q z t) u) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → ∀ t, Φ q (y,0) t = (y,0)) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivAt (Φ q z)
      (geodesicPhaseField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
        (metricOperatorField (conformalReferenceMatrix g L q)) (Φ q z t)) t) ∧
  ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → (Φ q (y,0) 1).1 = y) ∧
  (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B →
    HasFDerivAt (fun z => (Φ q z 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) ∧
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → ∀ v w : R3,
    fderiv ℝ (fderiv ℝ (fun z => (Φ q z 1).1)) (y,0) (0,w) (0,v) =
      -coordinateConnectionField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
        (metricOperatorField (conformalReferenceMatrix g L q)) y v w

def conformalReferenceGramFrameOperatorJoint (g : MatrixField) (L : ℝ)
    (p : ℝ × R3) : R3 →L[ℝ] R3 :=
  frameOperator (metricGramFrame (conformalReferenceOperatorJoint g L p))

theorem contDiff_conformalReferenceGramFrameOperatorJoint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) :
    ContDiff ℝ ∞ (conformalReferenceGramFrameOperatorJoint g L) :=
  contDiff_metricGramFrameOperator _ (contDiff_conformalReferenceOperatorJoint g hg L)
    (conformalReferenceOperatorJoint_pos g hg L)

theorem conformalReferenceGramFrameOperatorJoint_bijective
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (p : ℝ × R3) :
    Function.Bijective (conformalReferenceGramFrameOperatorJoint g L p) :=
  frameOperator_bijective _ _
    (metricGramFrame_isMetricOrthonormalFrame _
      (conformalReferenceOperatorJoint_symmetric g hg L p)
      (conformalReferenceOperatorJoint_pos g hg L p))

/-- Literal framed normalized endpoint metric of this precise chosen family. -/
def conformalReferenceFramedNormalMetric (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) :
    ℝ × ((R3 × ℝ) × R3) → R3 →L[ℝ] R3 :=
  parameterFramedNormalizedEndpointMetric (fun p => (Φ p.1 p.2 1).1)
    (conformalReferenceOperatorJoint g L) (conformalReferenceGramFrameOperatorJoint g L)

theorem conformalReferenceFramedNormalMetric_eq (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (p : (R3 × ℝ) × R3) :
    conformalReferenceFramedNormalMetric g L Φ (q,p) =
      framedNormalizedEndpointMetric (fun z => (Φ q z 1).1)
        (metricOperatorField (conformalReferenceMatrix g L q))
        (fun y => frameOperator (metricGramFrame
          (metricOperatorField (conformalReferenceMatrix g L q) y))) p := rfl

theorem contDiff_conformalReferenceFramedNormalMetric (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) :
    ContDiff ℝ ∞ (conformalReferenceFramedNormalMetric g L Φ) :=
  contDiff_parameterFramedNormalizedEndpointMetric _ _ _ hΘ
    (contDiff_conformalReferenceOperatorJoint g hg L)
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L)

/-- Actual radial cancellation from this same endpoint's first and second jets. -/
theorem conformalReferenceFramedNormalMetric_zero_radialJet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B) (z : R3) :
    conformalReferenceFramedNormalMetric g L Φ (q,((y,0),z)) =
      ContinuousLinearMap.id ℝ R3 ∧
    HasDerivAt (fun r : ℝ => conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z))) 0 0 := by
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,hvalue,hfirst,hsecond⟩
  let M : R3 → R3 →L[ℝ] R3 := metricOperatorField (conformalReferenceMatrix g L q)
  let Q : R3 → R3 →L[ℝ] R3 := inverseMetricField M
  let Θ : R3 × R3 → R3 := fun a => (Φ q a 1).1
  let F : R3 → R3 →L[ℝ] R3 := fun a => frameOperator (metricGramFrame (M a))
  have hM := (conformalReference_slice_data g hg L q).1
  have hsym := (conformalReference_slice_data g hg L q).2.2.1
  have hpos := (conformalReference_slice_data g hg L q).2.2.2.1
  have hMQ := (conformalReference_slice_data g hg L q).2.2.2.2
  have hΘq : ContDiff ℝ ∞ Θ := hΘ.comp (contDiff_const.prodMk contDiff_id)
  have hzero : Θ (y,0) = y := hvalue q hq y hy
  have hD : HasFDerivAt Θ
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0) :=
    hfirst q hq y hy
  have hH : ∀ X Y : R3,
      fderiv ℝ (fderiv ℝ Θ) (y,0) (0,X) (0,Y) = -coordinateConnectionField Q M y X Y := by
    intro X Y
    have h := hsecond q hq y hy Y X
    rw [conformalReference_coordinateConnection_symmetric g hg L q y Y X] at h
    exact h
  have hframe : IsMetricOrthonormalFrame (M y) (metricGramFrame (M y)) :=
    metricGramFrame_isMetricOrthonormalFrame _ (hsym y) (hpos y)
  have hraw : HasDerivAt (fun r : ℝ => normalizedEndpointMetric Θ M ((y,r),F y z)) 0 0 :=
    hasDerivAt_normalizedEndpointMetric_zero Θ M hΘq hM y (F y z)
      (coordinateConnectionField Q M y) hzero hD hH
      (coordinateConnectionField_metric_compatible Q M hM hsym hMQ y)
  exact ⟨framedNormalizedEndpointMetric_zero Θ M (fun a => metricGramFrame (M a))
    y z hzero hD hframe,
    hasDerivAt_framedNormalizedEndpointMetric_zero Θ M F y z hraw⟩

/-- Full closed dilation, center, signed radius and spatial cylinder. -/
def conformalReferenceFramedMetricRoom (y0 : R3) (ε : ℝ) :
    Set (ℝ × ((R3 × ℝ) × R3)) :=
  Icc (0 : ℝ) 1 ×ˢ ((closedBall y0 ε ×ˢ Icc (-ε) ε) ×ˢ closedBall (0 : R3) 2)

/-- A single chosen family, one signed room and all finite-order bounds. -/
theorem exists_compact_parameter_conformalReference_framed_normal_metric
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ),
      ConformalReferenceGeodesicEndpointData g L y0 Φ B ∧ 0 < ε ∧ 0 ≤ C ∧
      ContDiff ℝ ∞ (conformalReferenceGramFrameOperatorJoint g L) ∧
      (∀ p, Function.Bijective (conformalReferenceGramFrameOperatorJoint g L p)) ∧
      ContDiff ℝ ∞ (conformalReferenceFramedNormalMetric g L Φ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε →
        ∀ z ∈ closedBall (0 : R3) 2,
          (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z) ∈ B ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            HasDerivAt (Φ q (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z))
              (geodesicPhaseField
                (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
                (metricOperatorField (conformalReferenceMatrix g L q))
                (Φ q (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z) t)) t) ∧
          conformalReferenceFramedNormalMetric g L Φ (q,((y,0),z)) =
            ContinuousLinearMap.id ℝ R3 ∧
          HasDerivAt (fun s : ℝ => conformalReferenceFramedNormalMetric g L Φ (q,((y,s),z))) 0 0 ∧
          ‖conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) -
            ContinuousLinearMap.id ℝ R3‖ ≤ C*r^2 ∧
          ‖conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) -
            ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ) ∧
          (∀ u : R3, (1/2 : ℝ)*‖u‖^2 ≤
            inner ℝ (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) u) u) ∧
          ∀ u v : R3, |inner ℝ (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) u) v| ≤
            (3/2 : ℝ)*‖u‖*‖v‖) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ conformalReferenceFramedMetricRoom y0 ε,
          ‖iteratedFDeriv ℝ j (conformalReferenceFramedNormalMetric g L Φ) p‖ ≤ D := by
  obtain ⟨Φ,B,hData⟩ :=
    exists_smooth_conformalReference_geodesic_endpoint_velocity_secondJet g hg L y0
  have hSaved : ConformalReferenceGeodesicEndpointData g L y0 Φ B := hData
  rcases hData with ⟨hB,hy0,hΦ,hinit,hadd,hstat,hODE,hΘ,hvalue,hfirst,hsecond⟩
  let F := conformalReferenceGramFrameOperatorJoint g L
  let G := conformalReferenceFramedNormalMetric g L Φ
  have hF : ContDiff ℝ ∞ F := contDiff_conformalReferenceGramFrameOperatorJoint g hg L
  have hG : ContDiff ℝ ∞ G := contDiff_conformalReferenceFramedNormalMetric g hg L Φ hΘ
  obtain ⟨ε0,hε0,hphase⟩ := exists_commonRadius_parameter_framed_phase_domain B hB y0 hy0
    F hF.continuous (Icc (0 : ℝ) 1) isCompact_Icc
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
  have hz0 : (0 : R3) ∈ closedBall (0 : R3) 2 := by simp
  have hc (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ε0) :
      (y,0) ∈ B := by
    simpa only [zero_smul] using hphase q hq y hy 0 (by simpa using hε0.le) 0 hz0
  let H : (ℝ × (R3 × R3)) × ℝ → R3 →L[ℝ] R3 :=
    fun p => G (p.1.1,((p.1.2.1,p.2),p.1.2.2))
  have hH : ContDiff ℝ ∞ H := hG.comp
    (contDiff_fst.fst.prodMk
      ((contDiff_fst.snd.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd.snd))
  let K : Set (ℝ × (R3 × R3)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ε0 ×ˢ closedBall (0 : R3) 2)
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hj (p : ℝ × (R3 × R3)) (hp : p ∈ K) :
      HasDerivAt (fun r : ℝ => H (p,r)) 0 0 := by
    have hy : ‖p.2.1-y0‖ ≤ ε0 := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    exact (conformalReferenceFramedNormalMetric_zero_radialJet g hg L y0 Φ B hSaved
      p.1 hp.1 p.2.1 (hc p.1 hp.1 p.2.1 hy) p.2.2).2
  obtain ⟨C,hC,hquad⟩ := exists_compact_uniform_radial_quadratic_bound H hH K hK ε0 hε0.le hj
  obtain ⟨ε,hε,hεle,hsmall⟩ := exists_common_radius_quadratic_le_half ε0 C hε0 hC
  refine ⟨Φ,B,ε,C,hSaved,hε,hC,hF,
    conformalReferenceGramFrameOperatorJoint_bijective g hg L,hG,?_,?_⟩
  · intro q hq y hy r hr z hz
    have hy0' : ‖y-y0‖ ≤ ε0 := hy.trans hεle
    have hr0 : |r| ≤ ε0 := hr.trans hεle
    have hin : (y,r • F (q,y) z) ∈ B := hphase q hq y hy0' r hr0 z hz
    have hjet := conformalReferenceFramedNormalMetric_zero_radialJet g hg L y0 Φ B hSaved
      q hq y (hc q hq y hy0') z
    have hp : (q,(y,z)) ∈ K :=
      ⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hy0',hz⟩
    have hb : ‖G (q,((y,r),z)) - ContinuousLinearMap.id ℝ R3‖ ≤ C*r^2 := by
      simpa only [H,G,hjet.1] using hquad (q,(y,z)) hp r hr0
    have hh := hb.trans (hsmall r hr)
    exact ⟨hin,hODE q hq _ hin,hjet.1,hjet.2,hb,hh,
      inner_lower_bound_of_norm_sub_id_le_half _ hh,
      inner_upper_bound_of_norm_sub_id_le_half _ hh⟩
  · apply exists_compact_uniform_iteratedFDeriv_bound G hG
      (conformalReferenceFramedMetricRoom y0 ε)
    exact isCompact_Icc.prod
      (((isCompact_closedBall _ _).prod isCompact_Icc).prod (isCompact_closedBall _ _))

end OAI.AnisotropicCalderon.ConnectionError
