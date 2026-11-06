import Calderon.FischerConnectionTransport
import Calderon.BaseDensityAdjoint
import Calderon.ReferenceDensityBounds

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FischerDensityIntegration
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic
  FischerConnectionTransport BaseDensityAdjoint SmoothMetricFrame ReferenceDensityBounds

def weightedCoordinateDivergence (rho : R3 → ℝ) (X : R3 → R3) (x : R3) : ℝ :=
  ∑ i : Fin 3, directionalDeriv (coordinateDirection i) (fun y => rho y * (X y) i) x

lemma contDiff_vectorComponent (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => (X x) i) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) i : R3 →L[ℝ] ℝ).contDiff.comp hX

lemma vector_eq_sum_coordinateDirection (v : R3) :
    v = ∑ i : Fin 3, v i • coordinateDirection i := by
  simpa only [coordinateDirection,PiLp.basisFun_apply,PiLp.basisFun_repr] using
    ((PiLp.basisFun 2 ℝ (Fin 3)).sum_repr v).symm

lemma directionalDeriv_variable_eq_sum (P : R3 → ℝ) (X : R3 → R3) (x : R3) :
    fderiv ℝ P x (X x) = ∑ i : Fin 3, (X x) i * directionalDeriv (coordinateDirection i) P x := by
  conv_lhs => rw [vector_eq_sum_coordinateDirection (X x)]
  simp only [map_sum,map_smul,smul_eq_mul,directionalDeriv]

theorem compact_weighted_scalar_variable_adjoint (rho P : R3 → ℝ) (X : R3 → R3)
    (hr : ContDiff ℝ ∞ rho) (hP : ContDiff ℝ ∞ P) (hX : ContDiff ℝ ∞ X)
    (hcompact : HasCompactSupport P) :
    (∫ x : R3, rho x * fderiv ℝ P x (X x)) =
      -(∫ x : R3, weightedCoordinateDivergence rho X x * P x) := by
  have hi : ∀ i : Fin 3, Integrable (fun x => rho x * (X x) i *
      directionalDeriv (coordinateDirection i) P x) := by
    intro i
    exact ((hr.continuous.mul (contDiff_vectorComponent X hX i).continuous).mul
      (contDiff_directionalDeriv _ P hP).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_directionalDeriv _ P hcompact).mul_left
  have hj : ∀ i : Fin 3, Integrable (fun x =>
      directionalDeriv (coordinateDirection i) (fun y => rho y * (X y) i) x * P x) := by
    intro i
    exact ((contDiff_directionalDeriv _ _ (hr.mul (contDiff_vectorComponent X hX i))).continuous.mul
      hP.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have he : (fun x => rho x * fderiv ℝ P x (X x)) =
      fun x => ∑ i : Fin 3, rho x * (X x) i * directionalDeriv (coordinateDirection i) P x := by
    funext x
    rw [directionalDeriv_variable_eq_sum,Finset.mul_sum]
    simp only [mul_assoc]
  have hf : (fun x => weightedCoordinateDivergence rho X x * P x) =
      fun x => ∑ i : Fin 3,
        directionalDeriv (coordinateDirection i) (fun y => rho y * (X y) i) x * P x := by
    funext x
    simp only [weightedCoordinateDivergence,Finset.sum_mul]
  rw [he,hf,integral_finsetSum _ (fun i _ => hi i),integral_finsetSum _ (fun i _ => hj i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := compact_weighted_first_adjoint (coordinateDirection i) rho (fun y => (X y) i)
    P (fun _ => (1 : ℝ)) hr (contDiff_vectorComponent X hX i) hP contDiff_const hcompact
  simpa only [Real.inner_apply,mul_one,smul_eq_mul] using h

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma contDiff_fischerPair (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have h : (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) =
      fun x => polynomialFamilyFischerBilinear b d (c x) (z x) := by
    funext x
    rw [fischerInner_finitePolynomialField,polynomialFamilyFischerBilinear_apply]
  rw [h]
  exact ((polynomialFamilyFischerBilinear b d).contDiff.comp hc).clm_apply hz

lemma hasCompactSupport_fischerPair (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : HasCompactSupport c) :
    HasCompactSupport (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp only [fischerInner_finitePolynomialField,hx,Pi.zero_apply,zero_mul,Finset.sum_const_zero]

theorem compact_reference_fischer_covariant_contraction (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho)
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, rho x *
      (fischerInner (referenceCovariantPolynomialDerivative g L lam b c x (X x)) (finitePolynomialField d z x) +
        fischerInner (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (X x)))) =
      -(∫ x : R3, weightedCoordinateDivergence rho X x *
        fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have h := compact_weighted_scalar_variable_adjoint rho
    (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) X hr
    (contDiff_fischerPair b d c z hc hz) hX (hasCompactSupport_fischerPair b d c z hcompact)
  simpa only [referenceCovariantPolynomialDerivative_fischer_compatible g hg L lam b d c z hc hz] using h

theorem compact_reference_metric_fischer_covariant_contraction (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (X : R3 → R3) (hX : ContDiff ℝ ∞ X)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (fischerInner (referenceCovariantPolynomialDerivative g L lam b c x (X x)) (finitePolynomialField d z x) +
        fischerInner (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (X x)))) =
      -(∫ x : R3, weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y)) X x *
        fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  exact compact_reference_fischer_covariant_contraction g hg L lam _
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id))
    X hX b d c z hc hz hcompact

theorem compact_reference_frame_fischer_covariant_contraction (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (a : Fin 3)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (fischerInner (referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) a))
          (finitePolynomialField d z x) +
        fischerInner (finitePolynomialField b c x)
          (referenceCovariantPolynomialDerivative g L lam d z x (referenceMetricGramFrame g L (lam,x) a)))) =
      -(∫ x : R3, weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y))
        (fun y => referenceMetricGramFrame g L (lam,y) a) x *
          fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) :=
  compact_reference_metric_fischer_covariant_contraction g hg L lam _
    (contDiff_referenceMetricGramFrame_slice g hg L lam a) b d c z hc hz hcompact

end OAI.AnisotropicCalderon.FischerDensityIntegration
