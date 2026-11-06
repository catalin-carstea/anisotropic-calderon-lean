import Calderon.FischerCovectorAdjunction
import Calderon.MetricFrameTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.WeightedFischerSquare
open RadiusProfile ConformalDepth AngularPolynomial SphereHarmonic MetricOperator
  MovingFrameConnection FischerConnectionTransport FischerDensityIntegration
  FischerCovectorAdjunction MetricFrameTrace SmoothMetricFrame ReferenceDensityBounds

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative

variable {ι : Type*} [Fintype ι]

def covariantDerivativePolynomialFamily (b : ι → MvPolynomial (Fin 3) ℝ) :
    ι ⊕ (Fin 3 × Fin 3 × ι) → MvPolynomial (Fin 3) ℝ
  | .inl j => b j
  | .inr a => X a.2.1 * pderiv a.1 (b a.2.2)

def covariantDerivativeCoefficientFamily (g : MatrixField) (L lam : ℝ)
    (c : R3 → ι → ℝ) (V : R3 → R3) (x : R3) : ι ⊕ (Fin 3 × Fin 3 × ι) → ℝ
  | .inl j => (fderiv ℝ c x (V x)) j
  | .inr a => -referenceFrameConnectionCoefficient g L lam x (V x) a.1 a.2.1 * c x a.2.2

lemma referenceCovariantPolynomialDerivative_eq_finite_augmented (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (V : R3 → R3) (x : R3) :
    referenceCovariantPolynomialDerivative g L lam b c x (V x) =
      finitePolynomialField (covariantDerivativePolynomialFamily b)
        (covariantDerivativeCoefficientFamily g L lam c V) x := by
  simp only [referenceCovariantPolynomialDerivative, finitePolynomialFieldDerivative,
    referenceFrameAngularPolynomial, CurvatureSkew.polynomialMatrixVectorField,
    finitePolynomialField, Fintype.sum_sum_type, Fintype.sum_prod_type,
    covariantDerivativePolynomialFamily, covariantDerivativeCoefficientFamily,
    smul_eq_C_mul, map_sum, pderiv_C_mul, Finset.mul_sum, map_neg, map_mul,
    neg_mul, Finset.sum_neg_distrib]
  apply congrArg (fun z : MvPolynomial (Fin 3) ℝ =>
    (∑ j : ι, C ((fderiv ℝ c x (V x)) j) * b j) + -z)
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro t ht
  apply Finset.sum_congr rfl; intro j hj
  rw [mul_assoc, mul_left_comm (X t) (C (c x j)), mul_assoc]

lemma contDiff_covariantDerivativeCoefficientFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (c : R3 → ι → ℝ) (V : R3 → R3)
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (covariantDerivativeCoefficientFamily g L lam c V) := by
  apply contDiff_pi.mpr
  intro j
  rcases j with j | ⟨a,t,j⟩
  · exact contDiff_pi.mp (contDiff_variableCoefficientDerivative c V hc hV) j
  · exact (contDiff_referenceFrameConnectionCoefficient_variable g hg L lam V hV a t).neg.mul
      (contDiff_pi.mp hc j)

lemma contDiff_referenceCovariantPolynomialDerivative_fischer_square
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (V : R3 → R3)
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (V x))
      (referenceCovariantPolynomialDerivative g L lam b c x (V x))) := by
  simp only [referenceCovariantPolynomialDerivative_eq_finite_augmented]
  exact contDiff_fischerPair _ _ _ _
    (contDiff_covariantDerivativeCoefficientFamily g hg L lam c V hc hV)
    (contDiff_covariantDerivativeCoefficientFamily g hg L lam c V hc hV)

def referenceWeightedPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x V : R3) : MvPolynomial (Fin 3) ℝ :=
  C s * referenceCovariantPolynomialDerivative g L lam b c x V +
    C (k * fderiv ℝ f x V) * finitePolynomialField b c x

lemma fischerInner_weighted_square (q p : MvPolynomial (Fin 3) ℝ) (s w : ℝ) :
    fischerInner (C s*q+C w*p) (C s*q+C w*p) =
      s^2*fischerInner q q + 2*s*w*fischerInner q p + w^2*fischerInner p p := by
  simp only [fischerInner_add_left,fischerInner_add_right,fischerInner_C_mul_left,
    fischerInner_C_mul_right,fischerInner_symm p q]
  ring

lemma contDiff_referenceWeightedPolynomialDerivative_fischer_square
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (V : R3 → R3) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (V x))
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (V x))) := by
  simp only [referenceWeightedPolynomialDerivative,fischerInner_weighted_square]
  have hw : ContDiff ℝ ∞ (fun x => k*fderiv ℝ f x (V x)) :=
    contDiff_const.mul ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply hV)
  exact ((contDiff_const.mul
    (contDiff_referenceCovariantPolynomialDerivative_fischer_square g hg L lam b c V hc hV)).add
    ((contDiff_const.mul hw).mul
      (contDiff_referenceCovariantPolynomialDerivative_fischer_left g hg L lam V hV b b c c hc hc))).add
    ((hw.pow 2).mul (contDiff_fischerPair b b c c hc hc))

lemma hasCompactSupport_referenceWeightedPolynomialDerivative_fischer_square
    (g : MatrixField) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (f : R3 → ℝ) (k s : ℝ) (V : R3 → R3)
    (hc : HasCompactSupport c) :
    HasCompactSupport (fun x => fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (V x))
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (V x))) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hD0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  simp only [referenceWeightedPolynomialDerivative,
    referenceCovariantPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero g L lam b c x (V x) hc0 hD0,
    finitePolynomialField_eq_zero_of_coeff_eq_zero b c x hc0, mul_zero, add_zero, fischerInner_zero_left]

def referenceWeightedFrameEnergy (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, fischerInner
    (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))
    (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))

lemma integrable_referenceWeightedFrameEnergy (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k s : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    Integrable (fun x => rho x * referenceWeightedFrameEnergy g L lam b c f k s x) := by
  have hi (i : Fin 3) : Integrable (fun x => rho x * fischerInner
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))
      (referenceWeightedPolynomialDerivative g L lam b c f k s x (referenceMetricGramFrame g L (lam,x) i))) :=
    (hr.mul (contDiff_referenceWeightedPolynomialDerivative_fischer_square g hg L lam b c f k s _ hc hf
      (contDiff_referenceMetricGramFrame_slice g hg L lam i)).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_referenceWeightedPolynomialDerivative_fischer_square g L lam b c f k s _ hcompact).mul_left
  simpa only [referenceWeightedFrameEnergy,Finset.mul_sum] using
    integrable_finset_sum Finset.univ (fun i _ => hi i)

lemma fderiv_fischer_square_metricFrameGradient (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (f : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (x : R3) :
    fderiv ℝ (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) x
      (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f x) =
    ∑ i : Fin 3, 2*fderiv ℝ f x (referenceMetricGramFrame g L (lam,x) i) *
      fischerInner (referenceCovariantPolynomialDerivative g L lam b c x
        (referenceMetricGramFrame g L (lam,x) i)) (finitePolynomialField b c x) := by
  simp only [metricFrameGradient,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [referenceCovariantPolynomialDerivative_fischer_compatible g hg L lam b b c c hc hc]
  rw [fischerInner_symm (finitePolynomialField b c x)]
  ring

lemma referenceWeightedFrameEnergy_sub (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (f : R3 → ℝ) (k : ℝ) (hc : ContDiff ℝ ∞ c) (x : R3) :
    referenceWeightedFrameEnergy g L lam b c f k (-1) x -
      referenceWeightedFrameEnergy g L lam b c f k 1 x =
    -2*k*fderiv ℝ (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) x
      (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f x) := by
  rw [fderiv_fischer_square_metricFrameGradient g hg L lam b c f hc]
  simp only [referenceWeightedFrameEnergy,referenceWeightedPolynomialDerivative,fischerInner_weighted_square,
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem compact_referenceWeightedFrameEnergy_square_difference
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    (∫ x : R3, rho x * referenceWeightedFrameEnergy g L lam b c f k (-1) x) =
      (∫ x : R3, rho x * referenceWeightedFrameEnergy g L lam b c f k 1 x) +
        2*k*(∫ x : R3, weightedCoordinateDivergence rho
          (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f) x *
            fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  have hi := integrable_referenceWeightedFrameEnergy g hg L lam rho hr.continuous b c f k (-1) hc hf hcompact
  have hj := integrable_referenceWeightedFrameEnergy g hg L lam rho hr.continuous b c f k 1 hc hf hcompact
  have h := compact_weighted_scalar_variable_adjoint rho
    (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x))
    (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f) hr
    (contDiff_fischerPair b b c c hc hc)
    (contDiff_metricFrameGradient _ f (fun i => contDiff_referenceMetricGramFrame_slice g hg L lam i) hf)
    (hasCompactSupport_fischerPair b b c c hcompact)
  have he : (fun x => rho x * referenceWeightedFrameEnergy g L lam b c f k (-1) x -
      rho x * referenceWeightedFrameEnergy g L lam b c f k 1 x) =
    fun x => (-2*k)*(rho x*fderiv ℝ
      (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField b c y)) x
      (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f x)) := by
    funext x
    rw [← mul_sub,referenceWeightedFrameEnergy_sub g hg L lam b c f k hc]
    ring
  have hd : (∫ x : R3, rho x * referenceWeightedFrameEnergy g L lam b c f k (-1) x) -
      (∫ x : R3, rho x * referenceWeightedFrameEnergy g L lam b c f k 1 x) =
      2*k*(∫ x : R3, weightedCoordinateDivergence rho
        (metricFrameGradient (fun y => referenceMetricGramFrame g L (lam,y)) f) x *
          fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
    rw [← integral_sub hi hj, he, integral_const_mul, h]
    ring
  linarith

theorem compact_referenceWeightedFrameEnergy_hessian_square_difference
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (f : R3 → ℝ)
    (k : ℝ) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) * referenceWeightedFrameEnergy g L lam b c f k (-1) x) =
      (∫ x : R3, referenceDensityFamily g L (lam,x) * referenceWeightedFrameEnergy g L lam b c f k 1 x) +
      (∫ x : R3, referenceDensityFamily g L (lam,x) *
        (2*k*∑ i : Fin 3, coordinateHessian f (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
          (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
          fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) := by
  have h := compact_referenceWeightedFrameEnergy_square_difference g hg L lam
    (fun x => referenceDensityFamily g L (lam,x))
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)) b c f k hc hf hcompact
  simp only [reference_weightedCoordinateDivergence_metricFrameGradient_eq_hessian_trace g hg L lam f hf] at h
  rw [h]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem compact_referenceLogRadius_weightedFrameEnergy_square_difference
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (profileP k : ℕ)
    (hδ : 0 < δ) (hR : 0 < R)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R profileP L) (k : ℝ) (-1) x) =
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      referenceWeightedFrameEnergy g L lam b c (referenceLogRadius δ R profileP L) (k : ℝ) 1 x) +
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (2*(k : ℝ)*∑ i : Fin 3, coordinateHessian (referenceLogRadius δ R profileP L)
        (fun X Y => referenceConnectionFamily g L (lam,x) X Y) x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) i)) *
      fischerInner (finitePolynomialField b c x) (finitePolynomialField b c x)) :=
  compact_referenceWeightedFrameEnergy_hessian_square_difference g hg L lam b c
    (referenceLogRadius δ R profileP L) (k : ℝ) hc
    (contDiff_log_referenceRadius δ R profileP L hδ hR) hcompact

end OAI.AnisotropicCalderon.WeightedFischerSquare
