import Calderon.MetricFrameDivergence
import Calderon.FischerCovectorAdjunction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ContractedFischerAdjunction
open RadiusProfile ConformalDepth AngularPolynomial SphereHarmonic MetricOperator
  MovingFrameConnection FischerConnectionTransport FischerDensityIntegration
  FischerCovectorAdjunction MetricFrameDivergence SmoothMetricFrame ReferenceDensityBounds
  PolynomialSlotCompatibility FiniteCovectorTransport BaseDensityAdjoint

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  MetricOperator.metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def referenceTensorPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (x V : R3) (i j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceCovectorPolynomialDerivative g L lam (fun a t => b a i t) c x V j -
    ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x V a i) *
      finitePolynomialField (fun t => b t a j) c x

lemma referenceTensorPolynomialDerivative_fischer_left_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x V : R3) (i j : Fin 3) :
    fischerInner (referenceTensorPolynomialDerivative g L lam b c x V i j) (finitePolynomialField d z x) =
    fischerInner (referenceCovectorPolynomialDerivative g L lam (fun a t => b a i t) c x V j)
      (finitePolynomialField d z x) - ∑ a : Fin 3, referenceFrameConnectionCoefficient g L lam x V a i *
        fischerInner (finitePolynomialField (fun t => b t a j) c x) (finitePolynomialField d z x) := by
  simp only [referenceTensorPolynomialDerivative,fischerInner_sub_left,
    fischerInner_finset_sum_left,fischerInner_C_mul_left]

lemma contDiff_referenceTensorPolynomialDerivative_fischer_left (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => fischerInner
      (referenceTensorPolynomialDerivative g L lam b c x (V x) i j) (finitePolynomialField d z x)) := by
  simp_rw [referenceTensorPolynomialDerivative_fischer_left_eq]
  apply (contDiff_referenceCovectorPolynomialDerivative_fischer_left g hg L lam V hV _ d c z hc hz j).sub
  exact ContDiff.sum (fun a _ =>
    (contDiff_referenceFrameConnectionCoefficient_variable g hg L lam V hV a i).mul
      (contDiff_fischerPair _ _ c z hc hz))

lemma hasCompactSupport_referenceTensorPolynomialDerivative_fischer_left_second
    (g : MatrixField) (L lam : ℝ) (V : R3 → R3)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hz : HasCompactSupport z) (i j : Fin 3) :
    HasCompactSupport (fun x => fischerInner
      (referenceTensorPolynomialDerivative g L lam b c x (V x) i j) (finitePolynomialField d z x)) := by
  apply hz.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz0
  apply hx
  rw [finitePolynomialField_eq_zero_of_coeff_eq_zero d z x hz0,fischerInner_zero_right]

lemma integrable_referenceTensorPolynomialDerivative_fischer_right (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (i j : Fin 3) : Integrable (fun x => rho x * fischerInner
      (finitePolynomialField b c x) (referenceTensorPolynomialDerivative g L lam d z x (V x) i j)) := by
  have h : Integrable (fun x => rho x * fischerInner
      (referenceTensorPolynomialDerivative g L lam d z x (V x) i j) (finitePolynomialField b c x)) :=
    (hr.mul (contDiff_referenceTensorPolynomialDerivative_fischer_left g hg L lam V hV d b z c hz hc i j).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_referenceTensorPolynomialDerivative_fischer_left_second g L lam V d b z c hcompact i j).mul_left
  convert h using 1
  funext x
  rw [fischerInner_symm]

lemma contDiff_weightedCoordinateDivergence (rho : R3 → ℝ) (V : R3 → R3)
    (hr : ContDiff ℝ ∞ rho) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (weightedCoordinateDivergence rho V) :=
  ContDiff.sum (fun i _ => contDiff_directionalDeriv (coordinateDirection i)
    (fun y => rho y * (V y) i) (hr.mul (contDiff_vectorComponent V hV i)))

lemma frame_connection_trace_cancellation (w : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hw : ∀ v a b, w v a b = -w v b a) (P : Fin 3 → ℝ) :
    (∑ i : Fin 3, (∑ a : Fin 3, w a a i) * P i) =
      -(∑ i : Fin 3, ∑ a : Fin 3, w i a i * P a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro a ha
  rw [hw i i a,neg_mul]

lemma referenceTensor_contraction_eq_row_add_divergence (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceTensorPolynomialDerivative g L lam d z x (referenceMetricGramFrame g L (lam,x) i) i j)) =
    (∑ i : Fin 3, referenceDensityFamily g L (lam,x) * ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceCovectorPolynomialDerivative g L lam (fun a t => d a i t) z x
        (referenceMetricGramFrame g L (lam,x) i) j)) +
    (∑ i : Fin 3, weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y))
      (fun y => referenceMetricGramFrame g L (lam,y) i) x * finiteCovectorFischerPair b (fun a t => d a i t) c z x) := by
  have h (j : Fin 3) := frame_connection_trace_cancellation
    (fun v a t => referenceFrameConnectionCoefficient g L lam x (referenceMetricGramFrame g L (lam,x) v) a t)
    (fun v a t => referenceFrameConnectionCoefficient_skew g hg L lam x _ a t)
    (fun i => fischerInner (finitePolynomialField (fun a => b a j) c x)
      (finitePolynomialField (fun a => d a i j) z x))
  simp only [referenceTensorPolynomialDerivative,fischerInner_sub_right,fischerInner_sum_right,
    fischerInner_C_mul_right,Finset.sum_sub_distrib,Finset.mul_sum,finiteCovectorFischerPair,
    reference_weightedCoordinateDivergence_gramFrame g hg L lam] at *
  simp only [Fin.sum_univ_three] at *
  linear_combination -referenceDensityFamily g L (lam,x) * h 0 -
    referenceDensityFamily g L (lam,x) * h 1 - referenceDensityFamily g L (lam,x) * h 2

theorem compact_reference_contracted_tensor_fischer_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) i) j)
      (finitePolynomialField (fun a => d a i j) z x))) =
    -(∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceTensorPolynomialDerivative g L lam d z x (referenceMetricGramFrame g L (lam,x) i) i j))) := by
  let rho := fun x => referenceDensityFamily g L (lam,x)
  have hr : ContDiff ℝ ∞ rho :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  have he (i : Fin 3) : ContDiff ℝ ∞ (fun x => e x i) :=
    contDiff_referenceMetricGramFrame_slice g hg L lam i
  let A := fun i x => rho x * ∑ j : Fin 3, fischerInner
    (referenceCovectorPolynomialDerivative g L lam b c x (e x i) j)
    (finitePolynomialField (fun a => d a i j) z x)
  let B := fun i x => rho x * ∑ j : Fin 3, fischerInner
    (finitePolynomialField (fun a => b a j) c x)
    (referenceCovectorPolynomialDerivative g L lam (fun a t => d a i t) z x (e x i) j)
  let D := fun i x => weightedCoordinateDivergence rho (fun y => e y i) x *
    finiteCovectorFischerPair b (fun a t => d a i t) c z x
  have hA (i : Fin 3) : Integrable (A i) := by
    simp only [A,Finset.mul_sum]
    exact integrable_finset_sum _ (fun j _ => integrable_referenceCovectorPolynomialDerivative_fischer_left
      g hg L lam rho hr.continuous _ (he i) b _ c z hc hz hcompact j)
  have hB (i : Fin 3) : Integrable (B i) := by
    simp only [B,Finset.mul_sum]
    exact integrable_finset_sum _ (fun j _ => integrable_referenceCovectorPolynomialDerivative_fischer_right
      g hg L lam rho hr.continuous _ (he i) _ _ c z hc hz hcompact j)
  have hD (i : Fin 3) : Integrable (D i) :=
    ((contDiff_weightedCoordinateDivergence rho _ hr (he i)).continuous.mul
      (contDiff_finiteCovectorFischerPair b _ c z hc hz).continuous).integrable_of_hasCompactSupport (hasCompactSupport_finiteCovectorFischerPair b _ c z hcompact).mul_left
  have hi (i : Fin 3) : (∫ x, A i x) = -(∫ x, B i x) - (∫ x, D i x) :=
    compact_reference_covector_fischer_adjoint g hg L lam rho hr _ (he i) b _ c z hc hz hcompact
  have hs : (∫ x, ∑ i : Fin 3, A i x) =
      -(∫ x, ∑ i : Fin 3, B i x) - (∫ x, ∑ i : Fin 3, D i x) := by
    rw [integral_finsetSum _ (fun i _ => hA i),integral_finsetSum _ (fun i _ => hB i),
      integral_finsetSum _ (fun i _ => hD i),← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have hBsum : Integrable (fun x => ∑ i : Fin 3, B i x) := integrable_finset_sum _ (fun i _ => hB i)
  have hDsum : Integrable (fun x => ∑ i : Fin 3, D i x) := integrable_finset_sum _ (fun i _ => hD i)
  have hright : (fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceTensorPolynomialDerivative g L lam d z x (e x i) i j)) =
      fun x => (∑ i : Fin 3, B i x) + ∑ i : Fin 3, D i x :=
    funext (fun x => referenceTensor_contraction_eq_row_add_divergence g hg L lam b d c z x)
  have hleft : (fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (e x i) j)
      (finitePolynomialField (fun a => d a i j) z x)) = fun x => ∑ i : Fin 3, A i x := by
    funext x; simp only [A,Finset.mul_sum]
  change (∫ x, rho x * _) = -(∫ x, rho x * _)
  rw [hleft,hright,integral_add hBsum hDsum]
  linarith

def referenceWeightedCovectorPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x V : R3) (j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C s * referenceCovectorPolynomialDerivative g L lam b c x V j +
    C (k * fderiv ℝ f x V) * finitePolynomialField (fun a => b a j) c x

def referenceWeightedTensorPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x V : R3) (i j : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C s * referenceTensorPolynomialDerivative g L lam b c x V i j +
    C (k * fderiv ℝ f x V) * finitePolynomialField (fun a => b a i j) c x

theorem compact_reference_contracted_weighted_tensor_fischer_adjoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → Fin 3 → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (f : R3 → ℝ) (k s : ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (referenceWeightedCovectorPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i) j)
      (finitePolynomialField (fun a => d a i j) z x))) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) * (∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceWeightedTensorPolynomialDerivative g L lam d z f k (-s) x
        (referenceMetricGramFrame g L (lam,x) i) i j))) := by
  let rho := fun x => referenceDensityFamily g L (lam,x)
  have hr : ContDiff ℝ ∞ rho :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  let e := fun x => referenceMetricGramFrame g L (lam,x)
  have he (i : Fin 3) : ContDiff ℝ ∞ (fun x => e x i) :=
    contDiff_referenceMetricGramFrame_slice g hg L lam i
  let A := fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
    (referenceCovectorPolynomialDerivative g L lam b c x (e x i) j)
    (finitePolynomialField (fun a => d a i j) z x)
  let B := fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
    (finitePolynomialField (fun a => b a j) c x)
    (referenceTensorPolynomialDerivative g L lam d z x (e x i) i j)
  let W := fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3,
    (k*fderiv ℝ f x (e x i)) * fischerInner
      (finitePolynomialField (fun a => b a j) c x) (finitePolynomialField (fun a => d a i j) z x)
  have hA : Integrable A := by
    simp only [A,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceCovectorPolynomialDerivative_fischer_left g hg L lam rho hr.continuous
        _ (he i) b _ c z hc hz hcompact j))
  have hB : Integrable B := by
    simp only [B,Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      integrable_referenceTensorPolynomialDerivative_fischer_right g hg L lam rho hr.continuous
        _ (he i) _ d c z hc hz hcompact i j))
  have hW : Integrable W := by
    simp only [W,Finset.mul_sum]
    apply integrable_finset_sum; intro i hi
    apply integrable_finset_sum; intro j hj
    have hdf : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (e x i)) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply (he i)
    have hweight : ContDiff ℝ ∞ (fun x => k * fderiv ℝ f x (e x i)) :=
      (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => k)).mul hdf
    exact (hr.continuous.mul (hweight.continuous.mul
      (contDiff_fischerPair (fun a => b a j) (fun a => d a i j) c z hc hz).continuous)).integrable_of_hasCompactSupport
        (hasCompactSupport_fischerPair (fun a => b a j) (fun a => d a i j) c z hcompact).mul_left.mul_left
  have hab : (∫ x : R3, A x) = -(∫ x : R3, B x) :=
    compact_reference_contracted_tensor_fischer_adjoint g hg L lam b d c z hc hz hcompact
  have hl : (fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (referenceWeightedCovectorPolynomialDerivative g L lam b c f k s x (e x i) j)
      (finitePolynomialField (fun a => d a i j) z x)) = fun x => s*A x+W x := by
    funext x
    simp only [referenceWeightedCovectorPolynomialDerivative,fischerInner_add_left,
      fischerInner_C_mul_left,A,W,Fin.sum_univ_three]
    ring
  have hright : (fun x => rho x * ∑ i : Fin 3, ∑ j : Fin 3, fischerInner
      (finitePolynomialField (fun a => b a j) c x)
      (referenceWeightedTensorPolynomialDerivative g L lam d z f k (-s) x (e x i) i j)) =
      fun x => (-s)*B x+W x := by
    funext x
    simp only [referenceWeightedTensorPolynomialDerivative,fischerInner_add_right,
      fischerInner_C_mul_right,B,W,Fin.sum_univ_three]
    ring
  change (∫ x : R3, rho x * _) = (∫ x : R3, rho x * _)
  rw [hl,hright,integral_add (hA.const_mul _) hW,integral_add (hB.const_mul _) hW,
    integral_const_mul,integral_const_mul,hab]
  ring

end OAI.AnisotropicCalderon.ContractedFischerAdjunction
