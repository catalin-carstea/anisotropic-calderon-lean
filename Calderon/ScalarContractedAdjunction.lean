import Calderon.ContractedFischerAdjunction
import Calderon.WeightedFischerSquare

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ScalarContractedAdjunction
open RadiusProfile ConformalDepth AngularPolynomial SphereHarmonic MetricOperator
  MovingFrameConnection FischerConnectionTransport FischerDensityIntegration
  FischerCovectorAdjunction MetricFrameDivergence SmoothMetricFrame ReferenceDensityBounds
  PolynomialSlotCompatibility FiniteCovectorTransport BaseDensityAdjoint
  ContractedFischerAdjunction WeightedFischerSquare

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  MetricOperator.metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma integrable_referenceCovariantPolynomialDerivative_fischer_left (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) : Integrable (fun x => rho x * fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x)) :=
  (hr.mul (contDiff_referenceCovariantPolynomialDerivative_fischer_left g hg L lam V hV b d c z hc hz).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_referenceCovariantPolynomialDerivative_fischer_left g L lam V b d c z hcompact).mul_left

lemma integrable_referenceCovariantPolynomialDerivative_fischer_right (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) : Integrable (fun x => rho x * fischerInner
      (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (V x))) := by
  have h : Integrable (fun x => rho x * fischerInner
      (referenceCovariantPolynomialDerivative g L lam d z x (V x)) (finitePolynomialField b c x)) :=
    (hr.mul (contDiff_referenceCovariantPolynomialDerivative_fischer_left g hg L lam V hV d b z c hz hc).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_referenceCovariantPolynomialDerivative_fischer_left_second g L lam V d b z c hcompact).mul_left
  convert h using 1
  funext x
  rw [fischerInner_symm]

lemma referenceCovector_contraction_eq_scalar_add_divergence (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, fischerInner
      (finitePolynomialField b c x)
      (referenceCovectorPolynomialDerivative g L lam d z x (referenceMetricGramFrame g L (lam,x) i) i)) =
    (∑ i : Fin 3, referenceDensityFamily g L (lam,x) * fischerInner
      (finitePolynomialField b c x)
      (referenceCovariantPolynomialDerivative g L lam (fun a => d a i) z x
        (referenceMetricGramFrame g L (lam,x) i))) +
    (∑ i : Fin 3, weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y))
      (fun y => referenceMetricGramFrame g L (lam,y) i) x *
      fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x)) := by
  have h := frame_connection_trace_cancellation
    (fun v a t => referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) v) a t)
    (fun v a t => referenceFrameConnectionCoefficient_skew g hg L lam x _ a t)
    (fun i => fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x))
  simp only [referenceCovectorPolynomialDerivative,fischerInner_sub_right,fischerInner_sum_right,
    fischerInner_C_mul_right,Finset.sum_sub_distrib,Finset.mul_sum,
    reference_weightedCoordinateDivergence_gramFrame g hg L lam] at *
  simp only [Fin.sum_univ_three] at *
  linear_combination -referenceDensityFamily g L (lam,x) * h

theorem compact_reference_contracted_covector_fischer_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i))
      (finitePolynomialField (fun a => d a i) z x))) =
    -(∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, fischerInner
      (finitePolynomialField b c x)
      (referenceCovectorPolynomialDerivative g L lam d z x (referenceMetricGramFrame g L (lam,x) i) i))) := by
  let rho := fun x => referenceDensityFamily g L (lam,x)
  have hr : ContDiff ℝ ∞ rho :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  have he (i : Fin 3) : ContDiff ℝ ∞ (fun x => e x i) :=
    contDiff_referenceMetricGramFrame_slice g hg L lam i
  let A := fun i x => rho x * fischerInner
    (referenceCovariantPolynomialDerivative g L lam b c x (e x i))
    (finitePolynomialField (fun a => d a i) z x)
  let B := fun i x => rho x * fischerInner
    (finitePolynomialField b c x)
    (referenceCovariantPolynomialDerivative g L lam (fun a => d a i) z x (e x i))
  let D := fun i x => weightedCoordinateDivergence rho (fun y => e y i) x *
    fischerInner (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x)
  have hA (i : Fin 3) : Integrable (A i) :=
    integrable_referenceCovariantPolynomialDerivative_fischer_left g hg L lam rho hr.continuous _ (he i) b _ c z hc hz hcompact
  have hB (i : Fin 3) : Integrable (B i) :=
    integrable_referenceCovariantPolynomialDerivative_fischer_right g hg L lam rho hr.continuous _ (he i) b _ c z hc hz hcompact
  have hD (i : Fin 3) : Integrable (D i) :=
    ((contDiff_weightedCoordinateDivergence rho _ hr (he i)).continuous.mul
      (contDiff_fischerPair b _ c z hc hz).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_fischerPair b _ c z hcompact).mul_left
  have hi (i : Fin 3) : (∫ x, A i x) = -(∫ x, B i x) - (∫ x, D i x) := by
    have h := compact_reference_frame_fischer_covariant_contraction g hg L lam i b (fun a => d a i) c z hc hz hcompact
    have heq : (fun x => rho x * (fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (e x i)) (finitePolynomialField (fun a => d a i) z x) +
      fischerInner (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam (fun a => d a i) z x (e x i)))) =
      fun x => A i x+B i x := by funext x; simp only [A,B,mul_add]
    change (∫ x, rho x * _) = -(∫ x, D i x) at h
    rw [heq,integral_add (hA i) (hB i)] at h
    linarith
  have hs : (∫ x, ∑ i : Fin 3, A i x) =
      -(∫ x, ∑ i : Fin 3, B i x) - (∫ x, ∑ i : Fin 3, D i x) := by
    rw [integral_finsetSum _ (fun i _ => hA i),integral_finsetSum _ (fun i _ => hB i),
      integral_finsetSum _ (fun i _ => hD i),← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have hBsum : Integrable (fun x => ∑ i : Fin 3, B i x) := integrable_finset_sum _ (fun i _ => hB i)
  have hDsum : Integrable (fun x => ∑ i : Fin 3, D i x) := integrable_finset_sum _ (fun i _ => hD i)
  have hright : (fun x => rho x * ∑ i : Fin 3, fischerInner
      (finitePolynomialField b c x)
      (referenceCovectorPolynomialDerivative g L lam d z x (e x i) i)) =
      fun x => (∑ i : Fin 3, B i x) + ∑ i : Fin 3, D i x :=
    funext (fun x => referenceCovector_contraction_eq_scalar_add_divergence g hg L lam b d c z x)
  have hleft : (fun x => rho x * ∑ i : Fin 3, fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (e x i))
      (finitePolynomialField (fun a => d a i) z x)) = fun x => ∑ i : Fin 3, A i x := by
    funext x; simp only [A,Finset.mul_sum]
  change (∫ x, rho x * _) = -(∫ x, rho x * _)
  rw [hleft,hright,integral_add hBsum hDsum]
  linarith

theorem compact_reference_contracted_weighted_covector_fischer_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))
      (finitePolynomialField (fun a => d a i) z x))) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, fischerInner
      (finitePolynomialField b c x)
      (referenceWeightedCovectorPolynomialDerivative g L lam d z f k (-s) x
        (referenceMetricGramFrame g L (lam,x) i) i))) := by
  let rho := fun x => referenceDensityFamily g L (lam,x)
  have hr : ContDiff ℝ ∞ rho :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  have he (i : Fin 3) : ContDiff ℝ ∞ (fun x => e x i) :=
    contDiff_referenceMetricGramFrame_slice g hg L lam i
  let A := fun x => rho x * ∑ i : Fin 3, fischerInner
    (referenceCovariantPolynomialDerivative g L lam b c x (e x i))
    (finitePolynomialField (fun a => d a i) z x)
  let B := fun x => rho x * ∑ i : Fin 3, fischerInner
    (finitePolynomialField b c x)
    (referenceCovectorPolynomialDerivative g L lam d z x (e x i) i)
  let W := fun x => rho x * ∑ i : Fin 3,
    (k*fderiv ℝ f x (e x i)) * fischerInner
      (finitePolynomialField b c x) (finitePolynomialField (fun a => d a i) z x)
  have hA : Integrable A := by
    simp only [A,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ =>
      integrable_referenceCovariantPolynomialDerivative_fischer_left g hg L lam rho hr.continuous
        _ (he i) b _ c z hc hz hcompact)
  have hB : Integrable B := by
    simp only [B,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ =>
      integrable_referenceCovectorPolynomialDerivative_fischer_right g hg L lam rho hr.continuous
        _ (he i) b d c z hc hz hcompact i)
  have hW : Integrable W := by
    simp only [W,Finset.mul_sum]
    apply integrable_finset_sum; intro i hi
    have hdf : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (e x i)) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply (he i)
    have hweight : ContDiff ℝ ∞ (fun x => k * fderiv ℝ f x (e x i)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => k)).mul hdf
    exact (hr.continuous.mul (hweight.continuous.mul
      (contDiff_fischerPair b (fun a => d a i) c z hc hz).continuous)).integrable_of_hasCompactSupport
        (hasCompactSupport_fischerPair b (fun a => d a i) c z hcompact).mul_left.mul_left
  have hab : (∫ x : R3, A x) = -(∫ x : R3, B x) :=
    compact_reference_contracted_covector_fischer_adjoint g hg L lam b d c z hc hz hcompact
  have hl : (fun x => rho x * ∑ i : Fin 3, fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (e x i))
      (finitePolynomialField (fun a => d a i) z x)) = fun x => s*A x+W x := by
    funext x
    simp only [referenceWeightedPolynomialDerivative,fischerInner_add_left,
      fischerInner_C_mul_left,A,W,Fin.sum_univ_three]
    ring
  have hright : (fun x => rho x * ∑ i : Fin 3, fischerInner
      (finitePolynomialField b c x)
      (referenceWeightedCovectorPolynomialDerivative g L lam d z f k (-s) x (e x i) i)) =
      fun x => (-s)*B x+W x := by
    funext x
    simp only [referenceWeightedCovectorPolynomialDerivative,fischerInner_add_right,
      fischerInner_C_mul_right,B,W,Fin.sum_univ_three]
    ring
  change (∫ x : R3, rho x * _) = (∫ x : R3, rho x * _)
  rw [hl,hright,integral_add (hA.const_mul _) hW,integral_add (hB.const_mul _) hW,
    integral_const_mul,integral_const_mul,hab]
  ring

end OAI.AnisotropicCalderon.ScalarContractedAdjunction
