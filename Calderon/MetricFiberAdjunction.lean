import Calderon.MetricFiberFischer
import Calderon.FischerDensityIntegration

noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricFiberAdjunction
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial
  FrameCurvaturePolynomial SmoothMetricFrame MetricFiberMeasure MetricFiberFischer
  FischerConnectionTransport FischerDensityIntegration ReferenceDensityBounds BaseDensityAdjoint

def referenceFiberPolynomialPair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (p q : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∫ v : R3,
    metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) p v *
    metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) q v
    ∂metricFrameProbability (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x))
      (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))

lemma referenceFiberPolynomialPair_eq (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (k : ℕ)
    (p q : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous k) :
    referenceFiberPolynomialPair g hg L lam x p q = normalizedFischerInner k p q :=
  reference_metricFramePolynomial_fiber_inner hF g hg L lam x k p q hp hq

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma referenceFiberPolynomialPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField d z x) =
      fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x) / sphereNormalization 3 k := by
  simpa only [normalizedFischerInner,Fintype.card_fin] using referenceFiberPolynomialPair_eq hF g hg L lam x k
    _ _ (finitePolynomialField_harmonicHomogeneous k b hb c x) (finitePolynomialField_harmonicHomogeneous k d hd z x)

lemma contDiff_referenceFiberPolynomialPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => referenceFiberPolynomialPair g hg L lam x
      (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  simp_rw [referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z]
  exact (contDiff_fischerPair b d c z hc hz).div_const _

lemma hasCompactSupport_referenceFiberPolynomialPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : HasCompactSupport c) :
    HasCompactSupport (fun x => referenceFiberPolynomialPair g hg L lam x
      (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  apply (hasCompactSupport_fischerPair b d c z hc).mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  rw [referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z,hzero,zero_div]

theorem fderiv_referenceFiberPolynomialPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (x V : R3) :
    fderiv ℝ (fun y => referenceFiberPolynomialPair g hg L lam y
      (finitePolynomialField b c y) (finitePolynomialField d z y)) x V =
      referenceFiberPolynomialPair g hg L lam x
        (referenceCovariantPolynomialDerivative g L lam b c x V) (finitePolynomialField d z x) +
      referenceFiberPolynomialPair g hg L lam x
        (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x V) := by
  have heq : (fun y => referenceFiberPolynomialPair g hg L lam y
      (finitePolynomialField b c y) (finitePolynomialField d z y)) =
      fun y => (sphereNormalization 3 k)⁻¹ * fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y) := by
    funext y
    rw [referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z]
    simp only [div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_mul ((contDiff_fischerPair b d c z hc hz).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [referenceCovariantPolynomialDerivative_fischer_compatible g hg L lam b d c z hc hz]
  rw [referenceFiberPolynomialPair_eq hF g hg L lam x k _ _
      (referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c x V)
      (finitePolynomialField_harmonicHomogeneous k d hd z x),
    referenceFiberPolynomialPair_eq hF g hg L lam x k _ _
      (finitePolynomialField_harmonicHomogeneous k b hb c x)
      (referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k hk d hd z x V)]
  simp only [normalizedFischerInner,Fintype.card_fin,div_eq_mul_inv]
  ring

theorem compact_referenceFiberPolynomialPair_covariant_contraction (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, rho x *
      (referenceFiberPolynomialPair g hg L lam x
        (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x) +
      referenceFiberPolynomialPair g hg L lam x
        (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (V x)))) =
      -(∫ x : R3, weightedCoordinateDivergence rho V x *
        referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField d z x)) := by
  have h := compact_weighted_scalar_variable_adjoint rho _ V hr
    (contDiff_referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z hc hz) hV
    (hasCompactSupport_referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z hcompact)
  simpa only [fderiv_referenceFiberPolynomialPair_finite hF g hg L lam k hk b d hb hd c z hc hz] using h

theorem integrable_compact_referenceFiberPolynomialPair_covariant_sum (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    Integrable (fun x : R3 => rho x *
      (referenceFiberPolynomialPair g hg L lam x
        (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x) +
      referenceFiberPolynomialPair g hg L lam x
        (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (V x)))) := by
  let P : R3 → ℝ := fun x => referenceFiberPolynomialPair g hg L lam x
    (finitePolynomialField b c x) (finitePolynomialField d z x)
  have hP := contDiff_referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z hc hz
  have hs := hasCompactSupport_referenceFiberPolynomialPair_finite hF g hg L lam k b d hb hd c z hcompact
  have heq : (fun x => rho x * fderiv ℝ P x (V x)) =
      fun x => ∑ i : Fin 3, rho x * (V x) i * directionalDeriv (coordinateDirection i) P x := by
    funext x
    rw [directionalDeriv_variable_eq_sum,Finset.mul_sum]
    simp only [mul_assoc]
  have hi : Integrable (fun x => rho x * fderiv ℝ P x (V x)) := by
    rw [heq]
    apply integrable_finset_sum
    intro i _
    exact ((hr.continuous.mul (contDiff_vectorComponent V hV i).continuous).mul
      (contDiff_directionalDeriv _ P hP).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_directionalDeriv _ P hs).mul_left
  simpa only [P,fderiv_referenceFiberPolynomialPair_finite hF g hg L lam k hk b d hb hd c z hc hz] using hi

theorem compact_reference_volumeFiber_covariant_contraction (hF : SphereFischerInner)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ i, b i ∈ harmonicHomogeneous k) (hd : ∀ i, d i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, referenceDensityFamily g L (lam,x) *
      (referenceFiberPolynomialPair g hg L lam x
        (referenceCovariantPolynomialDerivative g L lam b c x (V x)) (finitePolynomialField d z x) +
      referenceFiberPolynomialPair g hg L lam x
        (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x (V x)))) =
      -(∫ x : R3, weightedCoordinateDivergence (fun y => referenceDensityFamily g L (lam,y)) V x *
        referenceFiberPolynomialPair g hg L lam x (finitePolynomialField b c x) (finitePolynomialField d z x)) :=
  compact_referenceFiberPolynomialPair_covariant_contraction hF g hg L lam k hk _
    ((contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id))
    V hV b d hb hd c z hc hz hcompact

end OAI.AnisotropicCalderon.MetricFiberAdjunction
