import Calderon.ActualPrincipalErrorCoefficient
import Calderon.AmbientReferenceCovariantCore

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ReferenceFrameUniformComparison
open MetricOperator ConformalDepth RadiusProfile SmoothMetricFrame MovingFrameConnection
  FrameCurvaturePolynomial PrincipalCommutator ReferenceDensityBounds

/-- Actual dual coefficients for Euclidean coordinate directions. -/
def referenceCoordinateDualCoefficient (g : MatrixField) (L : ℝ) (k i : Fin 3)
    (z : ℝ × R3) : ℝ :=
  ⟪metricOperatorField (referenceMetric (dilatedMetric g z.1) L) z.2
      (coordinateDirection k), referenceMetricGramFrame g L z i⟫_ℝ

lemma contDiff_referenceCoordinateDualCoefficient (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (k i : Fin 3) :
    ContDiff ℝ ∞ (referenceCoordinateDualCoefficient g L k i) :=
  ((contDiff_referenceMetricOperator_joint g hg L).clm_apply contDiff_const).inner ℝ
    (contDiff_referenceMetricGramFrame g hg L i)

lemma referenceMetricGramFrame_spatial_fderiv_eq (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (j : Fin 3) (z : ℝ × R3) :
    fderiv ℝ (fun y => referenceMetricGramFrame g L (z.1,y) j) z.2 =
      (fderiv ℝ (fun w => referenceMetricGramFrame g L w j) z).comp
        (ContinuousLinearMap.inr ℝ ℝ R3) := by
  have hp : HasFDerivAt (fun y : R3 => (z.1,y))
      (ContinuousLinearMap.inr ℝ ℝ R3) z.2 := hasFDerivAt_prodMk_right z.1 z.2
  exact (((contDiff_referenceMetricGramFrame g hg L j).differentiable (by simp) z).hasFDerivAt.comp z.2 hp).fderiv

lemma contDiff_referenceMetricGramFrame_spatial_fderiv (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 =>
      fderiv ℝ (fun y => referenceMetricGramFrame g L (z.1,y) j) z.2) := by
  have he : (fun z : ℝ × R3 =>
      fderiv ℝ (fun y => referenceMetricGramFrame g L (z.1,y) j) z.2) =
      fun z => (fderiv ℝ (fun w => referenceMetricGramFrame g L w j) z).comp
        (ContinuousLinearMap.inr ℝ ℝ R3) :=
    funext (referenceMetricGramFrame_spatial_fderiv_eq g hg L j)
  rw [he]
  exact ((contDiff_referenceMetricGramFrame g hg L j).fderiv_right
    (m := ∞) (by simp)).clm_comp contDiff_const

/-- The source coefficient in an actual Gram-frame direction, jointly in the dilation parameter. -/
def referenceGramConnectionCoefficient (g : MatrixField) (L : ℝ) (i a b : Fin 3)
    (z : ℝ × R3) : ℝ :=
  referenceFrameConnectionCoefficient g L z.1 z.2 (referenceMetricGramFrame g L z i) a b

lemma contDiff_referenceGramConnectionCoefficient (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (i a b : Fin 3) :
    ContDiff ℝ ∞ (referenceGramConnectionCoefficient g L i a b) := by
  have hd := (contDiff_referenceMetricGramFrame_spatial_fderiv g hg L b).clm_apply
    (contDiff_referenceMetricGramFrame g hg L i)
  have hc := ((contDiff_referenceConnectionFamily g hg L).clm_apply
    (contDiff_referenceMetricGramFrame g hg L i)).clm_apply
    (contDiff_referenceMetricGramFrame g hg L b)
  exact ((contDiff_referenceMetricOperator_joint g hg L).clm_apply (hd.add hc)).inner ℝ
    (contDiff_referenceMetricGramFrame g hg L a)

/-- Constants precede every dilation and shrinking parameter; no beta derivative occurs. -/
theorem exists_reference_frame_comparison_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      (∀ k i, |referenceCoordinateDualCoefficient g L k i (lam,x)| ≤ B) ∧
      (∀ i a b, |referenceGramConnectionCoefficient g L i a b (lam,x)| ≤ C) := by
  obtain ⟨B,hB,hb⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 => referenceCoordinateDualCoefficient g L t.1 t.2)
    (fun t => (contDiff_referenceCoordinateDualCoefficient g hg L t.1 t.2).continuous) K hK
  obtain ⟨C,hC,hc⟩ := exists_uniform_bound_finite_family
    (fun t : Fin 3 × Fin 3 × Fin 3 => referenceGramConnectionCoefficient g L t.1 t.2.1 t.2.2)
    (fun t => (contDiff_referenceGramConnectionCoefficient g hg L t.1 t.2.1 t.2.2).continuous) K hK
  exact ⟨B,C,hB,hC,fun lam hlam x hx =>
    ⟨fun k i => hb lam hlam x hx (k,i),fun i a b => hc lam hlam x hx (i,a,b)⟩⟩

/-- The actual metric dual coefficients reconstruct the Euclidean coordinate vector. -/
lemma coordinateDirection_eq_reference_frame_sum (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (z : ℝ × R3) (k : Fin 3) :
    coordinateDirection k = ∑ i : Fin 3,
      referenceCoordinateDualCoefficient g L k i z • referenceMetricGramFrame g L z i :=
  (metricFrame_sum_coordinates _ _
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L z) (coordinateDirection k)).symm

end OAI.AnisotropicCalderon.ReferenceFrameUniformComparison
