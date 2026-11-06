import Calderon.FiniteCovectorTransport
import Calderon.ReferenceCovariantJets

set_option maxSynthPendingDepth 10
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.FischerCovectorAdjunction
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  CurvatureSkew MovingFrameConnection SmoothMetricFrame FrameCurvaturePolynomial
  FischerConnectionTransport PolynomialSlotCompatibility FiniteCovectorTransport
  FischerDensityIntegration ReferenceDensityBounds BaseDensityAdjoint

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric

lemma contDiff_frameConnectionCoefficient_variable
    (M : R3 → R3 →L[ℝ] R3) (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (V : R3 → R3) (hM : ContDiff ℝ ∞ M)
    (hGamma : ContDiff ℝ ∞ Gamma) (hE : ∀ i, ContDiff ℝ ∞ (fun x => e x i))
    (hV : ContDiff ℝ ∞ V) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => frameConnectionCoefficient M Gamma e x (V x) i j) := by
  exact (hM.clm_apply (((hE j).fderiv_right (m := ∞) (by simp)).clm_apply hV |>.add
    ((hGamma.clm_apply hV).clm_apply (hE j)))).inner ℝ (hE i)

lemma contDiff_referenceFrameConnectionCoefficient_variable (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (V : R3 → R3) (hV : ContDiff ℝ ∞ V) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x => referenceFrameConnectionCoefficient g L lam x (V x) i j) :=
  contDiff_frameConnectionCoefficient_variable _ _ _ V
    ((contDiff_referenceMetricOperator_joint g hg L).comp (contDiff_const.prodMk contDiff_id))
    ((contDiff_referenceConnectionFamily g hg L).comp (contDiff_const.prodMk contDiff_id))
    (fun i => contDiff_referenceMetricGramFrame_slice g hg L lam i) hV i j

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contDiff_variableCoefficientDerivative (c : R3 → ι → ℝ) (V : R3 → R3)
    (hc : ContDiff ℝ ∞ c) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ c x (V x)) :=
  (hc.fderiv_right (m := ∞) (by simp)).clm_apply hV

lemma hasCompactSupport_variableCoefficientDerivative (c : R3 → ι → ℝ) (V : R3 → R3)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => fderiv ℝ c x (V x)) := by
  apply (hc.fderiv (𝕜 := ℝ)).mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp [hx]

lemma hasCompactSupport_fischerPair_second (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hz : HasCompactSupport z) : HasCompactSupport (fun x =>
      fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have h := hasCompactSupport_fischerPair d b z c hz
  convert h using 1
  funext x
  exact fischerInner_symm _ _

lemma referenceCovariantPolynomialDerivative_fischer_left_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x V : R3) :
    fischerInner (referenceCovariantPolynomialDerivative g L lam b c x V) (finitePolynomialField d z x) =
      fischerInner (finitePolynomialFieldDerivative b c x V) (finitePolynomialField d z x) -
      ∑ a : Fin 3, ∑ t : Fin 3, referenceFrameConnectionCoefficient g L lam x V a t *
        fischerInner (finitePolynomialField (fun j => X t * pderiv a (b j)) c x)
          (finitePolynomialField d z x) := by
  simp only [finitePolynomialField_multiplication,finitePolynomialField_partial,
    referenceCovariantPolynomialDerivative,referenceFrameAngularPolynomial,polynomialMatrixVectorField,
    fischerInner_add_left,fischerInner_neg_left,fischerInner_finset_sum_left,
    mul_assoc,fischerInner_C_mul_left]
  rfl

lemma contDiff_referenceCovariantPolynomialDerivative_fischer_left (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x)) := by
  simp_rw [referenceCovariantPolynomialDerivative_fischer_left_eq]
  apply ContDiff.sub
  · exact contDiff_fischerPair b d (fun x => fderiv ℝ c x (V x)) z
      (contDiff_variableCoefficientDerivative c V hc hV) hz
  · apply ContDiff.sum
    intro a _
    apply ContDiff.sum
    intro t _
    exact (contDiff_referenceFrameConnectionCoefficient_variable g hg L lam V hV a t).mul
      (contDiff_fischerPair _ d c z hc hz)

lemma finitePolynomialField_eq_zero_of_coeff_eq_zero (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) (hc : c x = 0) : finitePolynomialField b c x = 0 := by
  simp [finitePolynomialField,hc]

lemma referenceCovariantPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero
    (g : MatrixField) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x V : R3) (hc : c x = 0) (hD : fderiv ℝ c x = 0) :
    referenceCovariantPolynomialDerivative g L lam b c x V = 0 := by
  rw [referenceCovariantPolynomialDerivative,finitePolynomialField_eq_zero_of_coeff_eq_zero b c x hc]
  simp [finitePolynomialFieldDerivative,hD,referenceFrameAngularPolynomial,polynomialMatrixVectorField]

lemma hasCompactSupport_referenceCovariantPolynomialDerivative_fischer_left (g : MatrixField)
    (L lam : ℝ) (V : R3 → R3) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : HasCompactSupport c) : HasCompactSupport (fun x => fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x)) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hD0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  rw [referenceCovariantPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero g L lam b c x (V x) hc0 hD0,
    fischerInner_zero_left]

lemma hasCompactSupport_referenceCovariantPolynomialDerivative_fischer_left_second (g : MatrixField)
    (L lam : ℝ) (V : R3 → R3) (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hz : HasCompactSupport z) : HasCompactSupport (fun x => fischerInner
      (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x)) := by
  apply hz.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz0
  apply hx
  rw [finitePolynomialField_eq_zero_of_coeff_eq_zero d z x hz0,fischerInner_zero_right]

lemma referenceCovectorPolynomialDerivative_fischer_left_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x V : R3) (i : Fin 3) :
    fischerInner (referenceCovectorPolynomialDerivative g L lam b c x V i) (finitePolynomialField d z x) =
      fischerInner (referenceCovariantPolynomialDerivative g L lam (fun j => b j i) c x V)
        (finitePolynomialField d z x) -
      ∑ a : Fin 3, referenceFrameConnectionCoefficient g L lam x V a i *
        fischerInner (finitePolynomialField (fun j => b j a) c x) (finitePolynomialField d z x) := by
  simp only [referenceCovectorPolynomialDerivative,fischerInner_sub_left,
    fischerInner_finset_sum_left,fischerInner_C_mul_left]

lemma contDiff_referenceCovectorPolynomialDerivative_fischer_left (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i) (finitePolynomialField d z x)) := by
  simp_rw [referenceCovectorPolynomialDerivative_fischer_left_eq]
  apply (contDiff_referenceCovariantPolynomialDerivative_fischer_left g hg L lam V hV _ d c z hc hz).sub
  apply ContDiff.sum
  intro a _
  exact (contDiff_referenceFrameConnectionCoefficient_variable g hg L lam V hV a i).mul
    (contDiff_fischerPair _ d c z hc hz)

lemma referenceCovectorPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero
    (g : MatrixField) (L lam : ℝ) (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x V : R3) (hc : c x = 0) (hD : fderiv ℝ c x = 0) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam b c x V i = 0 := by
  simp only [referenceCovectorPolynomialDerivative,
    referenceCovariantPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero g L lam _ c x V hc hD,
    finitePolynomialField_eq_zero_of_coeff_eq_zero _ c x hc,mul_zero,Finset.sum_const_zero,sub_zero]

lemma hasCompactSupport_referenceCovectorPolynomialDerivative_fischer_left (g : MatrixField)
    (L lam : ℝ) (V : R3 → R3) (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : HasCompactSupport c) (i : Fin 3) : HasCompactSupport (fun x => fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i) (finitePolynomialField d z x)) := by
  apply hc.mono'
  intro x hx
  by_contra hnot
  have hc0 := image_eq_zero_of_notMem_tsupport hnot
  have hD0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  simp only [Function.mem_support] at hx
  apply hx
  rw [referenceCovectorPolynomialDerivative_eq_zero_of_coeff_fderiv_eq_zero g L lam b c x (V x) hc0 hD0 i,
    fischerInner_zero_left]

lemma hasCompactSupport_referenceCovectorPolynomialDerivative_fischer_left_second (g : MatrixField)
    (L lam : ℝ) (V : R3 → R3) (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hz : HasCompactSupport z) (i : Fin 3) : HasCompactSupport (fun x => fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i) (finitePolynomialField d z x)) := by
  apply hz.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz0
  apply hx
  rw [finitePolynomialField_eq_zero_of_coeff_eq_zero d z x hz0,fischerInner_zero_right]

lemma integrable_referenceCovectorPolynomialDerivative_fischer_left (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (i : Fin 3) : Integrable (fun x => rho x * fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i) (finitePolynomialField d z x)) :=
  (hr.mul (contDiff_referenceCovectorPolynomialDerivative_fischer_left g hg L lam V hV b d c z hc hz i).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_referenceCovectorPolynomialDerivative_fischer_left g L lam V b d c z hcompact i).mul_left

lemma integrable_referenceCovectorPolynomialDerivative_fischer_right (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : Continuous rho)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) (i : Fin 3) : Integrable (fun x => rho x * fischerInner
      (finitePolynomialField b c x) (referenceCovectorPolynomialDerivative g L lam d z x (V x) i)) := by
  have h : Integrable (fun x => rho x * fischerInner
      (referenceCovectorPolynomialDerivative g L lam d z x (V x) i) (finitePolynomialField b c x)) :=
    (hr.mul (contDiff_referenceCovectorPolynomialDerivative_fischer_left g hg L lam V hV d b z c hz hc i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_referenceCovectorPolynomialDerivative_fischer_left_second g L lam V d b z c hcompact i).mul_left
  convert h using 1
  funext x
  rw [fischerInner_symm]

theorem compact_reference_covector_fischer_adjoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, rho x * (∑ i : Fin 3, fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i)
      (finitePolynomialField (fun j => d j i) z x))) =
      -(∫ x : R3, rho x * (∑ i : Fin 3, fischerInner
        (finitePolynomialField (fun j => b j i) c x)
        (referenceCovectorPolynomialDerivative g L lam d z x (V x) i))) -
      (∫ x : R3, weightedCoordinateDivergence rho V x * finiteCovectorFischerPair b d c z x) := by
  have hleft : Integrable (fun x => rho x * (∑ i : Fin 3, fischerInner
      (referenceCovectorPolynomialDerivative g L lam b c x (V x) i)
      (finitePolynomialField (fun j => d j i) z x))) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_referenceCovectorPolynomialDerivative_fischer_left
      g hg L lam rho hr.continuous V hV b _ c z hc hz hcompact i)
  have hright : Integrable (fun x => rho x * (∑ i : Fin 3, fischerInner
      (finitePolynomialField (fun j => b j i) c x)
      (referenceCovectorPolynomialDerivative g L lam d z x (V x) i))) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => integrable_referenceCovectorPolynomialDerivative_fischer_right
      g hg L lam rho hr.continuous V hV _ d c z hc hz hcompact i)
  have h := compact_reference_covector_fischer_contraction g hg L lam rho hr V hV b d c z hc hz hcompact
  simp_rw [Finset.sum_add_distrib,mul_add] at h
  rw [integral_add hleft hright] at h
  linarith

end OAI.AnisotropicCalderon.FischerCovectorAdjunction
