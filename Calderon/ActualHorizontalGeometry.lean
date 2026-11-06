import Calderon.ActualSupportLocalSecondForm
import Calderon.AmbientReferenceCovariantCore
import Calderon.SmoothSphereRotationBounds

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualHorizontalNormBridge
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  SmoothSphereFields SmoothAngularApplication SmoothSphereRotationProjection
  SmoothSphereRotationBounds SmoothMovingFrameFields AmbientReferenceCovariantCore
  MovingFrameConnection SmoothMetricFrame MetricOperator ConformalDepth RadiusProfile
  ReferenceDensityBounds ActualBalancedFirstPrincipalError ActualSupportLocalSecondForm
  SectionFiveErrorForms FischerDensityIntegration FrameCurvaturePolynomial

/-- The actual coframe, rather than an independently chosen inverse matrix. -/
def referenceCoFrameEntry (g : MatrixField) (L : ℝ) (k i : Fin 3)
    (q : ℝ × R3) : ℝ :=
  ⟪metricOperatorField (referenceMetric (dilatedMetric g q.1) L) q.2
    (coordinateDirection k), referenceMetricGramFrame g L q i⟫_ℝ

lemma contDiff_referenceCoFrameEntry (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (k i : Fin 3) : ContDiff ℝ ∞ (referenceCoFrameEntry g L k i) :=
  ((contDiff_referenceMetricOperator_joint g hg L).clm_apply contDiff_const).inner ℝ
    (contDiff_referenceMetricGramFrame g hg L i)

/-- A joint smooth realization of the exact sliced Gram connection coefficient. -/
def referenceFrameConnectionJoint (g : MatrixField) (L : ℝ)
    (X : ℝ × R3 → R3) (q : ℝ × R3) (i j : Fin 3) : ℝ :=
  ⟪metricOperatorField (referenceMetric (dilatedMetric g q.1) L) q.2
    (fderiv ℝ (fun z : ℝ × R3 => referenceMetricGramFrame g L z j) q (0,X q) +
      referenceConnectionFamily g L q (X q) (referenceMetricGramFrame g L q j)),
    referenceMetricGramFrame g L q i⟫_ℝ

lemma contDiff_referenceFrameConnectionJoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (X : ℝ × R3 → R3) (hX : ContDiff ℝ ∞ X) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun q => referenceFrameConnectionJoint g L X q i j) := by
  have he := contDiff_referenceMetricGramFrame g hg L j
  have hd : ContDiff ℝ ∞ (fun q : ℝ × R3 =>
      fderiv ℝ (fun z => referenceMetricGramFrame g L z j) q (0,X q)) :=
    (he.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const.prodMk hX)
  have hc := ((contDiff_referenceConnectionFamily g hg L).clm_apply hX).clm_apply he
  exact ((contDiff_referenceMetricOperator_joint g hg L).clm_apply (hd.add hc)).inner ℝ
    (contDiff_referenceMetricGramFrame g hg L i)

lemma fderiv_referenceGramFrame_slice_apply (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (q : ℝ × R3) (j : Fin 3) (X : R3) :
    fderiv ℝ (fun y : R3 => referenceMetricGramFrame g L (q.1,y) j) q.2 X =
      fderiv ℝ (fun z : ℝ × R3 => referenceMetricGramFrame g L z j) q (0,X) := by
  have hp : HasFDerivAt (fun y : R3 => (q.1,y))
      (ContinuousLinearMap.inr ℝ ℝ R3) q.2 := hasFDerivAt_prodMk_right q.1 q.2
  have h := ((contDiff_referenceMetricGramFrame g hg L j).differentiable
    (by simp) q).hasFDerivAt.comp q.2 hp
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using
    congrArg (fun T : R3 →L[ℝ] R3 => T X) h.fderiv

lemma referenceFrameConnectionJoint_eq (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (X : ℝ × R3 → R3) (q : ℝ × R3) (i j : Fin 3) :
    referenceFrameConnectionJoint g L X q i j =
      referenceFrameConnectionCoefficient g L q.1 q.2 (X q) i j := by
  unfold referenceFrameConnectionJoint referenceFrameConnectionCoefficient
    frameConnectionCoefficient covariantFrameDerivative
  rw [fderiv_referenceGramFrame_slice_apply g hg L q j (X q)]

/-- Every coefficient used by the comparison is bounded from actual compact geometry. -/
theorem exists_reference_geometry_uniform_bounds (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      (∀ i k, |frameEntry g L i k (lam,x)| ≤ M) ∧
      (∀ k i, |referenceCoFrameEntry g L k i (lam,x)| ≤ M) ∧
      (∀ k a b, |referenceFrameConnectionCoefficient g L lam x
        (coordinateDirection k) a b| ≤ M) ∧
      (∀ i a b, |referenceFrameConnectionCoefficient g L lam x
        (referenceMetricGramFrame g L (lam,x) i) a b| ≤ M) := by
  obtain ⟨Mf,hMf,hf⟩ := exists_frameEntry_uniform_two_jet_bound g hg L K hK
  obtain ⟨Me,hMe,he⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 => referenceCoFrameEntry g L t.1 t.2)
    (fun t => (contDiff_referenceCoFrameEntry g hg L t.1 t.2).continuous) K hK
  obtain ⟨Mc,hMc,hc⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun q =>
      referenceFrameConnectionJoint g L (fun _ => coordinateDirection t.1) q t.2.1 t.2.2)
    (fun t => (contDiff_referenceFrameConnectionJoint g hg L _ contDiff_const
      t.2.1 t.2.2).continuous) K hK
  obtain ⟨Mg,hMg,hgC⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 × Fin 3 => fun q =>
      referenceFrameConnectionJoint g L
        (fun z => referenceMetricGramFrame g L z t.1) q t.2.1 t.2.2)
    (fun t => (contDiff_referenceFrameConnectionJoint g hg L _
      (contDiff_referenceMetricGramFrame g hg L t.1) t.2.1 t.2.2).continuous) K hK
  refine ⟨Mf+Me+Mc+Mg,by linarith,?_⟩
  intro lam hlam x hx
  refine ⟨?_,?_,?_,?_⟩
  · intro i k
    exact (hf lam hlam x hx i k (.inl ())).trans (by linarith)
  · intro k i
    exact (he lam hlam x hx (k,i)).trans (by linarith)
  · intro k a b
    have h := hc lam hlam x hx (k,a,b)
    rw [referenceFrameConnectionJoint_eq g hg L] at h
    exact h.trans (by linarith)
  · intro i a b
    have h := hgC lam hlam x hx (i,a,b)
    rw [referenceFrameConnectionJoint_eq g hg L] at h
    exact h.trans (by linarith)

lemma coordinateDirection_eq_sum_referenceGramFrame (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (k : Fin 3) :
    coordinateDirection k = ∑ i : Fin 3,
      referenceCoFrameEntry g L k i (lam,x) • referenceMetricGramFrame g L (lam,x) i := by
  exact (metricFrame_sum_coordinates _ _
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))
    (coordinateDirection k)).symm

lemma referenceGramFrame_eq_sum_coordinateDirection (g : MatrixField)
    (L lam : ℝ) (x : R3) (i : Fin 3) :
    referenceMetricGramFrame g L (lam,x) i =
      ∑ k : Fin 3, frameEntry g L i k (lam,x) • coordinateDirection k :=
  vector_eq_sum_coordinateDirection _

lemma referenceFrameConnectionCoefficient_sum (g : MatrixField) (L lam : ℝ)
    (x : R3) (c : Fin 3 → ℝ) (X : Fin 3 → R3) (a b : Fin 3) :
    referenceFrameConnectionCoefficient g L lam x (∑ i, c i • X i) a b =
      ∑ i, c i * referenceFrameConnectionCoefficient g L lam x (X i) a b := by
  unfold referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    map_add,sum_inner,inner_add_left,real_inner_smul_left,Finset.sum_add_distrib,mul_add]

end OAI.AnisotropicCalderon.ActualHorizontalNormBridge
