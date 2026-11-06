import Calderon.CompactParameterReferenceFramedNormalMetric
import Calderon.NearIdentityPositiveMatrixExtension
import Calderon.MixedRadialDerivativeBounds
import Calderon.WeightedCommonSupportCoefficients
import Calderon.PositiveMatrixPointCalculus
import Mathlib.Topology.Order.DenselyOrdered

/-! UNCOMPILED author proposal. EXPANSION.md C1--C7 was sealed first.
The same Phi/B and entire original framed-metric package are retained. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

/-- Transparent packaging of the entire original joint framed-metric conclusion. -/
def ConformalReferenceFramedNormalMetricData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ) : Prop :=
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
      ‖iteratedFDeriv ℝ j (conformalReferenceFramedNormalMetric g L Φ) p‖ ≤ D

def referenceFramedNormalOperatorForCoefficients (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (p : (ℝ × (R3 × ℝ)) × R3) : R3 →L[ℝ] R3 :=
  conformalReferenceFramedNormalMetric g L Φ (p.1.1,(p.1.2,p.2))

def referenceFramedNormalMatrixForCoefficients (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (p : (ℝ × (R3 × ℝ)) × R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  operatorMatrixMap (referenceFramedNormalOperatorForCoefficients g L Φ p)

theorem referenceFramedNormalMatrixForCoefficients_eq (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (y z : R3) (r : ℝ) :
    referenceFramedNormalMatrixForCoefficients g L Φ ((q,(y,r)),z) =
      framedNormalizedEndpointMetricMatrix (fun a => (Φ q a 1).1)
        (metricOperatorField (conformalReferenceMatrix g L q))
        (fun a => frameOperator (metricGramFrame
          (metricOperatorField (conformalReferenceMatrix g L q) a))) ((y,r),z) := rfl

theorem referenceFramedNormalOperatorForCoefficients_symmetric (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (p : (ℝ × (R3 × ℝ)) × R3) (u v : R3) :
    inner ℝ (referenceFramedNormalOperatorForCoefficients g L Φ p u) v =
      inner ℝ (referenceFramedNormalOperatorForCoefficients g L Φ p v) u := by
  exact framedNormalizedEndpointMetric_symmetric
    (fun a => (Φ p.1.1 a 1).1)
    (metricOperatorField (conformalReferenceMatrix g L p.1.1))
    (fun a => frameOperator (metricGramFrame
      (metricOperatorField (conformalReferenceMatrix g L p.1.1) a)))
    (fun x => conformalReferenceOperatorJoint_symmetric g hg L (p.1.1,x))
    (p.1.2,p.2) u v

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def referenceCoefficientRadialReorder (F : (ℝ × (R3 × ℝ)) × R3 → V) :
    (ℝ × (R3 × R3)) × ℝ → V :=
  fun p => F ((p.1.1,(p.1.2.1,p.2)),p.1.2.2)

theorem contDiff_referenceCoefficientRadialReorder
    (F : (ℝ × (R3 × ℝ)) × R3 → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (referenceCoefficientRadialReorder F) :=
  hF.comp ((contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd.snd)

def referenceCoefficientNonradialRoom (y0 : R3) (ρ : ℝ) : Set (ℝ × (R3 × R3)) :=
  Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ closedBall (0 : R3) 2)

/-- Interior identities justify all q jets at both endpoints by continuity. -/
theorem compactMixedRadialBounds_referenceCoefficient_error
    (F : (ℝ × (R3 × ℝ)) × R3 → V) (hF : ContDiff ℝ ∞ F)
    (y0 : R3) (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ →
      ∀ z : R3, ‖z‖ ≤ 2 → F ((q,(y,0)),z) = 0)
    (hjet : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ →
      ∀ z : R3, ‖z‖ ≤ 2 → HasDerivAt (fun r : ℝ => F ((q,(y,r)),z)) 0 0) :
    CompactMixedRadialBounds (referenceCoefficientRadialReorder F)
      (referenceCoefficientNonradialRoom y0 ρ) ρ := by
  let s : Set (ℝ × (R3 × R3)) :=
    Ioo (0 : ℝ) 1 ×ˢ (ball y0 (2*ρ) ×ˢ ball (0 : R3) 2)
  have hs : IsOpen s := isOpen_Ioo.prod (isOpen_ball.prod isOpen_ball)
  have hQ : IsCompact (referenceCoefficientNonradialRoom y0 ρ) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hcl : closure s =
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (2*ρ) ×ˢ closedBall (0 : R3) 2) := by
    simp only [s,closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_ball y0 (by positivity : 2*ρ ≠ 0),closure_ball (0 : R3) (by norm_num : (2 : ℝ) ≠ 0)]
  have hQs : referenceCoefficientNonradialRoom y0 ρ ⊆ closure s := by
    intro p hp
    rw [hcl]
    exact ⟨hp.1,Metric.closedBall_subset_closedBall (by linarith : ρ ≤ 2*ρ) hp.2.1,hp.2.2⟩
  have hz : ∀ p ∈ s, referenceCoefficientRadialReorder F (p,0) = 0 := by
    intro p hp
    have hy : ‖p.2.1-y0‖ < 2*ρ := by simpa only [mem_ball,dist_eq_norm] using hp.2.1
    have hx : ‖p.2.2‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hp.2.2
    exact hzero p.1 ⟨hp.1.1.le,hp.1.2.le⟩ p.2.1 hy.le p.2.2 hx.le
  have hj : ∀ p ∈ s, HasDerivAt
      (fun r : ℝ => referenceCoefficientRadialReorder F (p,r)) 0 0 := by
    intro p hp
    have hy : ‖p.2.1-y0‖ < 2*ρ := by simpa only [mem_ball,dist_eq_norm] using hp.2.1
    have hx : ‖p.2.2‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hp.2.2
    exact hjet p.1 ⟨hp.1.1.le,hp.1.2.le⟩ p.2.1 hy.le p.2.2 hx.le
  exact compactMixedRadialBounds_of_zero_radial_jets _
    (contDiff_referenceCoefficientRadialReorder F hF) s _ hs hQ hQs hz hj ρ hρ.le

def JointReferenceCoefficientMixedBounds (y0 : R3) (ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ) : Prop :=
  ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
    ∀ p ∈ referenceCoefficientNonradialRoom y0 ρ, ∀ r : ℝ, |r| ≤ ρ →
      ‖parameterJetField j (referenceCoefficientRadialReorder (fun x => H x-1)) (p,r)‖ ≤ D*r^2 ∧
      ‖parameterJetField j (referenceCoefficientRadialReorder (fun x => a x-1)) (p,r)‖ ≤ D*r^2 ∧
      ‖parameterJetField j (referenceCoefficientRadialReorder (fun x => w x-1)) (p,r)‖ ≤ D*r^2 ∧
      ‖parameterJetField j (iteratedRadialDerivative 1
        (referenceCoefficientRadialReorder (fun x => H x-1))) (p,r)‖ ≤ D*|r| ∧
      ‖parameterJetField j (iteratedRadialDerivative 1
        (referenceCoefficientRadialReorder (fun x => a x-1))) (p,r)‖ ≤ D*|r| ∧
      ‖parameterJetField j (iteratedRadialDerivative 1
        (referenceCoefficientRadialReorder (fun x => w x-1))) (p,r)‖ ≤ D*|r| ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ N →
        ‖parameterJetField j (iteratedRadialDerivative k
          (referenceCoefficientRadialReorder (fun x => H x-1))) (p,r)‖ ≤ D ∧
        ‖parameterJetField j (iteratedRadialDerivative k
          (referenceCoefficientRadialReorder (fun x => a x-1))) (p,r)‖ ≤ D ∧
        ‖parameterJetField j (iteratedRadialDerivative k
          (referenceCoefficientRadialReorder (fun x => w x-1))) (p,r)‖ ≤ D

theorem jointReferenceCoefficientMixedBounds_of_individual (y0 : R3) (ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hH : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun x => H x-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ)
    (ha : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun x => a x-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ)
    (hw : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun x => w x-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ) :
    JointReferenceCoefficientMixedBounds y0 ρ H a w := by
  intro N
  obtain ⟨CH,hCH,hbH⟩ := hH N
  obtain ⟨Ca,hCa,hba⟩ := ha N
  obtain ⟨Cw,hCw,hbw⟩ := hw N
  have hHle : CH ≤ CH+Ca+Cw := by linarith
  have hale : Ca ≤ CH+Ca+Cw := by linarith
  have hwle : Cw ≤ CH+Ca+Cw := by linarith
  refine ⟨CH+Ca+Cw,by positivity,?_⟩
  intro j hj p hp r hr
  have bH := hbH j hj p hp r hr
  have ba := hba j hj p hp r hr
  have bw := hbw j hj p hp r hr
  refine ⟨bH.1.trans (mul_le_mul_of_nonneg_right hHle (sq_nonneg r)),
    ba.1.trans (mul_le_mul_of_nonneg_right hale (sq_nonneg r)),
    bw.1.trans (mul_le_mul_of_nonneg_right hwle (sq_nonneg r)),
    bH.2.1.trans (mul_le_mul_of_nonneg_right hHle (abs_nonneg r)),
    ba.2.1.trans (mul_le_mul_of_nonneg_right hale (abs_nonneg r)),
    bw.2.1.trans (mul_le_mul_of_nonneg_right hwle (abs_nonneg r)),?_⟩
  intro k hk hkN
  exact ⟨(bH.2.2 k hk hkN).trans hHle,(ba.2.2 k hk hkN).trans hale,
    (bw.2.2 k hk hkN).trans hwle⟩

theorem coefficientSpatialBump_eq_one_on_closed_two (z : R3) (hz : ‖z‖ ≤ 2) :
    coefficientSpatialBump z = 1 := by
  apply coefficientSpatialBump.one_of_mem_closedBall
  simpa only [coefficientSpatialBump,mem_closedBall,dist_zero_right] using hz

/-- Same flow, actual global positive extension and one radius for every mixed prefix. -/
theorem exists_compact_parameter_conformalReference_positive_coefficients
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
      (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (ℝ × (R3 × ℝ)) × R3 → ℝ),
      ConformalReferenceFramedNormalMetricData g L y0 Φ B ε C ∧
      0 < ρ ∧ 4*ρ ≤ ε ∧
      H = nearIdentityPositiveMatrixExtension (referenceFramedNormalOperatorForCoefficients g L Φ) ∧
      a = cutoffPrincipalCoefficient H ∧ w = cutoffVolumeDensity H ∧
      ContDiff ℝ ∞ H ∧ (∀ p, (H p).PosDef) ∧ ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ w ∧
      (∀ p : ℝ × (R3 × ℝ), ∀ z : R3, 3 ≤ ‖z‖ → a (p,z) = 0 ∧ w (p,z) = 0) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ →
        ∀ z ∈ closedBall (0 : R3) 2,
          H ((q,(y,r)),z) = referenceFramedNormalMatrixForCoefficients g L Φ ((q,(y,r)),z) ∧
          a ((q,(y,r)),z) = matrixPrincipalCoefficient
            (referenceFramedNormalMatrixForCoefficients g L Φ) ((q,(y,r)),z) ∧
          w ((q,(y,r)),z) = matrixVolumeDensity
            (referenceFramedNormalMatrixForCoefficients g L Φ) ((q,(y,r)),z)) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ 2*ρ → ∀ z : R3, ‖z‖ ≤ 2 →
        H ((q,(y,0)),z) = 1 ∧ a ((q,(y,0)),z) = 1 ∧ w ((q,(y,0)),z) = 1 ∧
        HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 ∧
        HasDerivAt (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ∧
        HasDerivAt (fun r : ℝ => w ((q,(y,r)),z)) 0 0) ∧
      (∃ lam Lam : ℝ, ∀ p ∈
        Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
        TauCeti.PDE.UniformlyEllipticOn (closedBall (0 : R3) 1)
          (fun z => a (p,z)) lam Lam) ∧
      JointReferenceCoefficientMixedBounds y0 ρ H a w := by
  obtain ⟨Φ,B,ε,C,hNormal⟩ :=
    exists_compact_parameter_conformalReference_framed_normal_metric g hg L y0
  have hSaved : ConformalReferenceFramedNormalMetricData g L y0 Φ B ε C := hNormal
  rcases hNormal with ⟨hEndpoint,hε,hC,hF,hbij,hG,hGeom,hAll⟩
  let Gop := referenceFramedNormalOperatorForCoefficients g L Φ
  let Gmat := referenceFramedNormalMatrixForCoefficients g L Φ
  have hGop : ContDiff ℝ ∞ Gop :=
    hG.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  let H := nearIdentityPositiveMatrixExtension Gop
  have hHs : ContDiff ℝ ∞ H := contDiff_nearIdentityPositiveMatrixExtension Gop hGop
  have hHP : ∀ p, (H p).PosDef := nearIdentityPositiveMatrixExtension_posDef Gop
    (referenceFramedNormalOperatorForCoefficients_symmetric g hg L Φ)
  let a := cutoffPrincipalCoefficient H
  let w := cutoffVolumeDensity H
  have ha : ContDiff ℝ ∞ a := contDiff_cutoffPrincipalCoefficient H hHs hHP
  have hw : ContDiff ℝ ∞ w := contDiff_cutoffVolumeDensity H hHs hHP
  obtain ⟨η,hη,hηε,hsmall⟩ := exists_common_radius_quadratic_le_half ε (2*C) hε (by positivity)
  let ρ : ℝ := η/4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have h4ρ : 4*ρ = η := by dsimp [ρ]; ring
  have hρε : 4*ρ ≤ ε := by rw [h4ρ]; exact hηε
  have hLocalH (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
      (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
      H ((q,(y,r)),z) = Gmat ((q,(y,r)),z) := by
    apply nearIdentityPositiveMatrixExtension_eq Gop
    rcases hGeom q hq y (hy.trans hρε) r (hr.trans hρε) z hz with
      ⟨_,_,_,_,hb,_,_,_⟩
    have hs := hsmall r (by simpa only [h4ρ] using hr)
    exact hb.trans (by nlinarith)
  have hraw (p : (ℝ × (R3 × ℝ)) × R3) (hz : ‖p.2‖ ≤ 2) :
      a p = matrixPrincipalCoefficient H p ∧ w p = matrixVolumeDensity H p := by
    have hb := coefficientSpatialBump_eq_one_on_closed_two p.2 hz
    simp [a,w,cutoffPrincipalCoefficient,cutoffVolumeDensity,hb]
  have hZeroJet (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 2*ρ)
      (z : R3) (hz : ‖z‖ ≤ 2) :
      H ((q,(y,0)),z) = 1 ∧ a ((q,(y,0)),z) = 1 ∧ w ((q,(y,0)),z) = 1 ∧
      HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 ∧
      HasDerivAt (fun r : ℝ => a ((q,(y,r)),z)) 0 0 ∧
      HasDerivAt (fun r : ℝ => w ((q,(y,r)),z)) 0 0 := by
    have hy4 : ‖y-y0‖ ≤ 4*ρ := by linarith
    have hzK : z ∈ closedBall (0 : R3) 2 := by
      simpa only [mem_closedBall,dist_zero_right] using hz
    rcases hGeom q hq y (hy4.trans hρε) 0 (by simpa using hε.le) z hzK with
      ⟨_,_,hzero,hjet,_,_,_,_⟩
    have hH0 : H ((q,(y,0)),z) = 1 := by
      rw [hLocalH q hq y hy4 0 (by simpa using (by positivity : 0 ≤ 4*ρ)) z hzK]
      change operatorMatrixMap (conformalReferenceFramedNormalMetric g L Φ (q,((y,0),z))) = 1
      rw [hzero,operatorMatrixMap_id]
    have hGjet : HasDerivAt (fun r : ℝ => Gmat ((q,(y,r)),z)) 0 0 := by
      have hd := operatorMatrixMap.hasFDerivAt.comp_hasDerivAt 0 hjet
      simp only [Function.comp_def,map_zero] at hd
      dsimp only [Gmat,referenceFramedNormalMatrixForCoefficients,
        referenceFramedNormalOperatorForCoefficients]
      convert hd using 1 <;> rfl
    have heq : (fun r : ℝ => H ((q,(y,r)),z)) =ᶠ[𝓝 (0 : ℝ)]
        (fun r : ℝ => Gmat ((q,(y,r)),z)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with r hr
      have hr' : |r| < ρ := by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hr
      exact hLocalH q hq y hy4 r (by linarith) z hzK
    have hHjet : HasDerivAt (fun r : ℝ => H ((q,(y,r)),z)) 0 0 :=
      hGjet.congr_of_eventuallyEq heq
    have hea : (fun r : ℝ => a ((q,(y,r)),z)) =
        matrixPrincipalCoefficient (fun r : ℝ => H ((q,(y,r)),z)) := by
      funext r
      exact (hraw ((q,(y,r)),z) hz).1
    have hew : (fun r : ℝ => w ((q,(y,r)),z)) =
        matrixVolumeDensity (fun r : ℝ => H ((q,(y,r)),z)) := by
      funext r
      exact (hraw ((q,(y,r)),z) hz).2
    have ha0 : a ((q,(y,0)),z) = 1 := by
      rw [(hraw ((q,(y,0)),z) hz).1]
      simp [matrixPrincipalCoefficient,matrixVolumeDensity,hH0]
    have hw0 : w ((q,(y,0)),z) = 1 := by
      rw [(hraw ((q,(y,0)),z) hz).2]
      simp [matrixVolumeDensity,hH0]
    refine ⟨hH0,ha0,hw0,hHjet,?_,?_⟩
    · rw [hea]
      exact hasDerivAt_matrixPrincipalCoefficient_zero _ 0 hHjet (hHP ((q,(y,0)),z))
    · rw [hew]
      exact hasDerivAt_matrixVolumeDensity_zero _ 0 hHjet (hHP ((q,(y,0)),z))
  have hMixedH : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun p => H p-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ := by
    apply compactMixedRadialBounds_referenceCoefficient_error _ (hHs.sub contDiff_const) y0 ρ hρ
    · intro q hq y hy z hz
      rw [(hZeroJet q hq y hy z hz).1,sub_self]
    · intro q hq y hy z hz
      simpa only [sub_zero] using ((hZeroJet q hq y hy z hz).2.2.2.1).sub_const 1
  have hMixeda : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun p => a p-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ := by
    apply compactMixedRadialBounds_referenceCoefficient_error _ (ha.sub contDiff_const) y0 ρ hρ
    · intro q hq y hy z hz
      rw [(hZeroJet q hq y hy z hz).2.1,sub_self]
    · intro q hq y hy z hz
      simpa only [sub_zero] using ((hZeroJet q hq y hy z hz).2.2.2.2.1).sub_const 1
  have hMixedw : CompactMixedRadialBounds (referenceCoefficientRadialReorder (fun p => w p-1))
      (referenceCoefficientNonradialRoom y0 ρ) ρ := by
    apply compactMixedRadialBounds_referenceCoefficient_error _ (hw.sub contDiff_const) y0 ρ hρ
    · intro q hq y hy z hz
      rw [(hZeroJet q hq y hy z hz).2.2.1,sub_self]
    · intro q hq y hy z hz
      simpa only [sub_zero] using ((hZeroJet q hq y hy z hz).2.2.2.2.2).sub_const 1
  obtain ⟨lam,Lam,hUE⟩ := exists_uniformlyElliptic_cutoffPrincipalCoefficient H hHs hHP
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ))
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc))
  refine ⟨Φ,B,ε,C,ρ,H,a,w,hSaved,hρ,hρε,rfl,rfl,rfl,hHs,hHP,ha,hw,?_,?_,
    hZeroJet,⟨lam,Lam,hUE⟩,
    jointReferenceCoefficientMixedBounds_of_individual y0 ρ H a w hMixedH hMixeda hMixedw⟩
  · intro p z hz
    exact ⟨cutoffPrincipalCoefficient_eq_zero_outside H (p,z) hz,
      cutoffVolumeDensity_eq_zero_outside H (p,z) hz⟩
  · intro q hq y hy r hr z hz
    have hloc := hLocalH q hq y hy r hr z hz
    have hz' : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    refine ⟨hloc,?_,?_⟩
    · rw [(hraw ((q,(y,r)),z) hz').1]
      simp only [matrixPrincipalCoefficient,matrixVolumeDensity,hloc,Gmat]
    · rw [(hraw ((q,(y,r)),z) hz').2]
      simp only [matrixVolumeDensity,hloc,Gmat]

end OAI.AnisotropicCalderon.ConnectionError
