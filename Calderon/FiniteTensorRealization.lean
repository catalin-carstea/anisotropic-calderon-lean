import Calderon.WeightedIndexedCurvature
import Calderon.ScalarContractedAdjunction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FiniteTensorRealization
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew
  MovingFrameConnection FischerConnectionTransport WeightedFischerSquare
  SmoothMetricFrame FrameCurvaturePolynomial FiniteCovariantCurvature
  PolynomialSlotCompatibility FullCovectorCurvature IndexedCovariantCurvature
  ContractedFischerAdjunction WeightedIndexedCurvature ScalarContractedAdjunction

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative
  finitePolynomialField finitePolynomialFieldDerivative referenceFrameAngularPolynomial
  referenceCovariantPolynomialDerivative

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [DecidableEq σ]

lemma referenceCovariantPolynomialDerivative_congr (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (h : ∀ x, finitePolynomialField b c x = finitePolynomialField d z x) (x V : R3) :
    referenceCovariantPolynomialDerivative g L lam b c x V =
      referenceCovariantPolynomialDerivative g L lam d z x V := by
  have heval : evaluatedReferencePolynomialField g L lam b c =
      evaluatedReferencePolynomialField g L lam d z := by
    funext v
    rw [evaluatedReferencePolynomialField_eq,evaluatedReferencePolynomialField_eq,h v.1]
  apply referenceMovingFramePolynomial_injective g hg L lam x
  intro v
  have hd := congrArg (fun u : R3 × R3 → ℝ => fderiv ℝ u (x,v)
    (V,-referenceConnectionFamily g L (lam,x) V v)) heval
  rw [fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam b c hc,
    fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam d z hz] at hd
  exact hd

def indexedPolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ) :
    (σ × ι) → σ → MvPolynomial (Fin 3) ℝ := fun a i => if a.1=i then b a.2 else 0

def indexedCoefficientFamily (c : R3 → σ → ι → ℝ) (x : R3) : σ × ι → ℝ :=
  fun a => c x a.1 a.2

lemma finitePolynomialField_indexed (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → σ → ι → ℝ) (x : R3) (i : σ) :
    finitePolynomialField (fun a => indexedPolynomialFamily b a i) (indexedCoefficientFamily c) x =
      finitePolynomialField b (fun y => c y i) x := by
  simp only [finitePolynomialField,indexedPolynomialFamily,indexedCoefficientFamily,
    Fintype.sum_prod_type]
  simp

lemma contDiff_indexedCoefficientFamily (c : R3 → σ → ι → ℝ)
    (hc : ∀ i, ContDiff ℝ ∞ (fun x => c x i)) :
    ContDiff ℝ ∞ (indexedCoefficientFamily c) := by
  apply contDiff_pi.mpr
  intro a
  exact contDiff_pi.mp (hc a.1) a.2

lemma hasCompactSupport_indexedCoefficientFamily (c : R3 → σ → ι → ℝ)
    (hc : HasCompactSupport c) : HasCompactSupport (indexedCoefficientFamily c) := by
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hc0
  apply hx
  funext a
  simp only [indexedCoefficientFamily,hc0,Pi.zero_apply]

def referenceWeightedIndexedCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) :
    R3 → Fin 3 → ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι) → ℝ := fun x i =>
  weightedDerivativeCoefficientFamily g L lam c f k t
    (fun y => referenceMetricGramFrame g L (lam,y) i) x

lemma contDiff_referenceWeightedIndexedCoefficientFamily (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (referenceWeightedIndexedCoefficientFamily g L lam c f k t) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_weightedDerivativeCoefficientFamily g hg L lam c f k t _ hc hf
    (contDiff_referenceMetricGramFrame_slice g hg L lam i)

lemma hasCompactSupport_referenceWeightedIndexedCoefficientFamily (g : MatrixField)
    (L lam : ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ) (hc : HasCompactSupport c) :
    HasCompactSupport (referenceWeightedIndexedCoefficientFamily g L lam c f k t) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  funext i a
  rcases a with a | a
  · rcases a with a | ⟨h,j,a⟩ <;>
      simp only [referenceWeightedIndexedCoefficientFamily,weightedDerivativeCoefficientFamily,
        joinedCoefficientFamily,Sum.elim_inl,Pi.smul_apply,covariantDerivativeCoefficientFamily,
        hd0,hc0,ContinuousLinearMap.zero_apply,Pi.zero_apply,smul_zero,mul_zero]
  · simp only [referenceWeightedIndexedCoefficientFamily,weightedDerivativeCoefficientFamily,
      joinedCoefficientFamily,Sum.elim_inr,Pi.smul_apply,hc0,Pi.zero_apply,smul_zero]

lemma finitePolynomialField_referenceWeighted_indexed (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) (i : Fin 3) :
    finitePolynomialField
      (fun a => indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)
      (indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)) x =
    referenceWeightedPolynomialDerivative g L lam b c f k t x (referenceMetricGramFrame g L (lam,x) i) := by
  rw [finitePolynomialField_indexed]
  exact (referenceWeightedPolynomialDerivative_eq_finite g L lam b c f k t _ x).symm

lemma finitePolynomialField_referenceWeighted_lowered (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) (i l : Fin 3) :
    finitePolynomialField
      (fun a => pderiv l (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i))
      (indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)) x =
    referenceWeightedCovectorPolynomialDerivative g L lam (fun a h => pderiv h (b a)) c f k t x
      (referenceMetricGramFrame g L (lam,x) i) l := by
  rw [finitePolynomialField_partial,finitePolynomialField_referenceWeighted_indexed,
    referenceWeightedCovectorPolynomialDerivative_partial]

lemma referenceCovectorPolynomialDerivative_referenceWeighted_lowered (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x V : R3) (j l : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam
      (fun a h => pderiv h (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a j))
      (indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)) x V l =
    referenceCovectorPolynomialDerivative g L lam (fun a h => pderiv h (weightedDerivativePolynomialFamily b a))
      (weightedDerivativeCoefficientFamily g L lam c f k t
        (fun y => referenceMetricGramFrame g L (lam,y) j)) x V l := by
  have hj := contDiff_referenceWeightedIndexedCoefficientFamily g hg L lam c f k t hc hf
  have hflatten := contDiff_indexedCoefficientFamily _ (contDiff_pi.mp hj)
  have hcomponent := contDiff_weightedDerivativeCoefficientFamily g hg L lam c f k t _ hc hf
    (contDiff_referenceMetricGramFrame_slice g hg L lam j)
  rw [referenceCovectorPolynomialDerivative_partial,referenceCovectorPolynomialDerivative_partial]
  apply congrArg (pderiv l)
  apply referenceCovariantPolynomialDerivative_congr g hg L lam _ _ _ _ hflatten hcomponent
  intro y
  rw [finitePolynomialField_indexed]
  rfl

lemma referenceWeightedTensorPolynomialDerivative_referenceWeighted_lowered (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s t : ℝ)
    (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (x : R3) (i j l : Fin 3) :
    referenceWeightedTensorPolynomialDerivative g L lam
      (fun a h q => pderiv q (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a h))
      (indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)) f k s x
      (referenceMetricGramFrame g L (lam,x) i) j l =
    referenceWeightedLoweredCovectorIndexedHessian g L lam b c f k s t x i j l := by
  simp only [referenceWeightedTensorPolynomialDerivative,referenceTensorPolynomialDerivative,
    referenceWeightedLoweredCovectorIndexedHessian,referenceWeightedCovectorPolynomialDerivative]
  rw [referenceCovectorPolynomialDerivative_referenceWeighted_lowered g hg L lam b c f k t hc hf]
  simp_rw [finitePolynomialField_referenceWeighted_lowered]
  rw [referenceWeightedCovectorPolynomialDerivative_partial g L lam b c f k t x
    (referenceMetricGramFrame g L (lam,x) j) l]
  rw [referenceWeightedPolynomialDerivative_eq_finite g L lam b c f k t
    (fun y => referenceMetricGramFrame g L (lam,y) j) x]
  simp only [finitePolynomialField_partial,referenceWeightedCovectorPolynomialDerivative]
  ring

def referenceWeightedTracePolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ) :
    Fin 3 × ((ι ⊕ (Fin 3 × Fin 3 × ι)) ⊕ ι) → MvPolynomial (Fin 3) ℝ := fun a =>
  ∑ i : Fin 3, pderiv i (indexedPolynomialFamily (weightedDerivativePolynomialFamily b) a i)

lemma finitePolynomialField_referenceWeighted_trace (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k t : ℝ) (x : R3) :
    finitePolynomialField (referenceWeightedTracePolynomialFamily b)
      (indexedCoefficientFamily (referenceWeightedIndexedCoefficientFamily g L lam c f k t)) x =
    ∑ i : Fin 3, referenceWeightedCovectorPolynomialDerivative g L lam
      (fun a h => pderiv h (b a)) c f k t x (referenceMetricGramFrame g L (lam,x) i) i := by
  unfold referenceWeightedTracePolynomialFamily
  simp only [finitePolynomialField,Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => by
    simpa only [finitePolynomialField] using
      finitePolynomialField_referenceWeighted_lowered g L lam b c f k t x i i)

lemma referenceWeightedTensorPolynomialDerivative_transpose (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x V : R3) (i j : Fin 3) :
    referenceWeightedTensorPolynomialDerivative g L lam (fun a h l => b a l h) c f k s x V i j =
      referenceWeightedTensorPolynomialDerivative g L lam b c f k s x V j i := by
  simp only [referenceWeightedTensorPolynomialDerivative,referenceTensorPolynomialDerivative,
    referenceCovectorPolynomialDerivative]
  ring

lemma finitePolynomialField_sum_family (b : ι → σ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) :
    finitePolynomialField (fun a => ∑ i : σ, b a i) c x =
      ∑ i : σ, finitePolynomialField (fun a => b a i) c x := by
  simp only [finitePolynomialField,Finset.smul_sum]
  exact Finset.sum_comm

lemma referenceCovariantPolynomialDerivative_sum_family (g : MatrixField) (L lam : ℝ)
    (b : ι → σ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x V : R3) :
    referenceCovariantPolynomialDerivative g L lam (fun a => ∑ i : σ, b a i) c x V =
      ∑ i : σ, referenceCovariantPolynomialDerivative g L lam (fun a => b a i) c x V := by
  simp only [referenceCovariantPolynomialDerivative,finitePolynomialField_sum_family]
  have hd : finitePolynomialFieldDerivative (fun a => ∑ i : σ, b a i) c x V =
      ∑ i : σ, finitePolynomialFieldDerivative (fun a => b a i) c x V := by
    simp only [finitePolynomialFieldDerivative,Finset.smul_sum]
    exact Finset.sum_comm
  rw [hd]
  have ha : referenceFrameAngularPolynomial g L lam x V (∑ i : σ, finitePolynomialField (fun a => b a i) c x) =
      ∑ i : σ, referenceFrameAngularPolynomial g L lam x V (finitePolynomialField (fun a => b a i) c x) :=
    referenceFrameAngularPolynomial_sum g L lam x V (fun i => finitePolynomialField (fun a => b a i) c x)
  rw [ha,Finset.sum_add_distrib]

lemma skew_tensor_trace_cancellation (w : Fin 3 → Fin 3 → ℝ)
    (hw : ∀ a i, w a i = -w i a) (T : Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ a : Fin 3, C (w a i) * T a i) +
      (∑ i : Fin 3, ∑ a : Fin 3, C (w a i) * T i a) = 0 := by
  have h : (∑ i : Fin 3, ∑ a : Fin 3, C (w a i) * T a i) =
      -(∑ i : Fin 3, ∑ a : Fin 3, C (w a i) * T i a) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro a ha
    rw [hw i a,map_neg,neg_mul]
  rw [h,neg_add_cancel]

lemma referenceWeightedPolynomialDerivative_tensorTrace (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (f : R3 → ℝ) (k s : ℝ) (x V : R3) :
    referenceWeightedPolynomialDerivative g L lam (fun a => ∑ i : Fin 3, b a i i) c f k s x V =
      ∑ i : Fin 3, referenceWeightedTensorPolynomialDerivative g L lam b c f k s x V i i := by
  have h := skew_tensor_trace_cancellation
    (fun a i => referenceFrameConnectionCoefficient g L lam x V a i)
    (fun a i => referenceFrameConnectionCoefficient_skew g hg L lam x V a i)
    (fun a i => finitePolynomialField (fun j => b j a i) c x)
  have hq := referenceCovariantPolynomialDerivative_sum_family g L lam (fun a i => b a i i) c x V
  have hu := finitePolynomialField_sum_family (fun a i => b a i i) c x
  simp only [referenceWeightedPolynomialDerivative,referenceWeightedTensorPolynomialDerivative,
    referenceTensorPolynomialDerivative,referenceCovectorPolynomialDerivative,
    Fin.sum_univ_three] at *
  rw [hq,hu]
  linear_combination C s * h

end OAI.AnisotropicCalderon.FiniteTensorRealization
