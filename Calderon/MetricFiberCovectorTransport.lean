import Calderon.MetricFiberAdjunction
import Calderon.FiniteCovectorTransport

noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.MetricFiberCovectorTransport
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial
  FrameCurvaturePolynomial SmoothMetricFrame MetricFiberMeasure MetricFiberFischer
  MetricFiberAdjunction MovingFrameConnection FischerConnectionTransport
  PolynomialSlotCompatibility FiniteCovectorTransport FischerDensityIntegration
  ReferenceDensityBounds BaseDensityAdjoint

def metricFrameCovectorPair (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (U V : Fin 3 → MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∫ v : R3, (∑ i : Fin 3, metricFramePolynomial M e (U i) v *
    metricFramePolynomial M e (V i) v) ∂metricFrameProbability M e he

lemma integrable_metricFrameCovectorPair_integrand (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (U V : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    Integrable (fun v : R3 => ∑ i : Fin 3, metricFramePolynomial M e (U i) v *
      metricFramePolynomial M e (V i) v) (metricFrameProbability M e he) :=
  integrable_finset_sum _ (fun i _ => integrable_metricFramePolynomial_fiber_pair M e he (U i) (V i))

lemma metricFrameCovectorPair_eq_sum (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (U V : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    metricFrameCovectorPair M e he U V = ∑ i : Fin 3,
      ∫ v : R3, metricFramePolynomial M e (U i) v * metricFramePolynomial M e (V i) v
        ∂metricFrameProbability M e he := by
  exact integral_finsetSum _ (fun i _ => integrable_metricFramePolynomial_fiber_pair M e he (U i) (V i))

lemma metricFrameCovectorPair_eq (hF : SphereFischerInner) (M : R3 →L[ℝ] R3)
    (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e) (k : ℕ)
    (U V : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hU : ∀ i, U i ∈ harmonicHomogeneous k) (hV : ∀ i, V i ∈ harmonicHomogeneous k) :
    metricFrameCovectorPair M e he U V = (∑ i : Fin 3, fischerInner (U i) (V i)) /
      sphereNormalization 3 k := by
  rw [metricFrameCovectorPair_eq_sum]
  simp_rw [metricFramePolynomial_fiber_inner hF M e he k _ _ (hU _) (hV _)]
  simp only [normalizedFischerInner,Fintype.card_fin,Finset.sum_div]

def referenceFiberCovectorPair (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (U V : Fin 3 → MvPolynomial (Fin 3) ℝ) : ℝ :=
  metricFrameCovectorPair (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
    (referenceMetricGramFrame g L (lam,x))
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)) U V

lemma referenceFiberCovectorPair_eq (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x : R3) (k : ℕ)
    (U V : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hU : ∀ i, U i ∈ harmonicHomogeneous k) (hV : ∀ i, V i ∈ harmonicHomogeneous k) :
    referenceFiberCovectorPair g hg L lam x U V = (∑ i : Fin 3, fischerInner (U i) (V i)) /
      sphereNormalization 3 k :=
  metricFrameCovectorPair_eq hF _ _ _ k U V hU hV

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma referenceFiberCovectorPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (hd : ∀ j i, d j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    referenceFiberCovectorPair g hg L lam x
      (fun i => finitePolynomialField (fun j => b j i) c x)
      (fun i => finitePolynomialField (fun j => d j i) z x) =
      finiteCovectorFischerPair b d c z x / sphereNormalization 3 k :=
  referenceFiberCovectorPair_eq hF g hg L lam x k _ _
    (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hb j i) c x)
    (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hd j i) z x)

lemma contDiff_referenceFiberCovectorPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (hd : ∀ j i, d j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun x => referenceFiberCovectorPair g hg L lam x
      (fun i => finitePolynomialField (fun j => b j i) c x)
      (fun i => finitePolynomialField (fun j => d j i) z x)) := by
  simp_rw [referenceFiberCovectorPair_finite hF g hg L lam k b d hb hd c z]
  exact (contDiff_finiteCovectorFischerPair b d c z hc hz).div_const _

lemma hasCompactSupport_referenceFiberCovectorPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (hd : ∀ j i, d j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : HasCompactSupport c) :
    HasCompactSupport (fun x => referenceFiberCovectorPair g hg L lam x
      (fun i => finitePolynomialField (fun j => b j i) c x)
      (fun i => finitePolynomialField (fun j => d j i) z x)) := by
  apply (hasCompactSupport_finiteCovectorFischerPair b d c z hc).mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  rw [referenceFiberCovectorPair_finite hF g hg L lam k b d hb hd c z,hzero,zero_div]

lemma referenceCovectorPolynomialDerivative_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam b c x V i ∈ harmonicHomogeneous k := by
  apply (harmonicHomogeneous k).sub_mem
    (referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k hk _ (fun j => hb j i) c x V)
  apply (harmonicHomogeneous k).sum_mem
  intro a _
  simpa only [smul_eq_C_mul] using (harmonicHomogeneous k).smul_mem
    (referenceFrameConnectionCoefficient g L lam x V a i)
    (finitePolynomialField_harmonicHomogeneous k _ (fun j => hb j a) c x)

theorem fderiv_referenceFiberCovectorPair_finite (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (hd : ∀ j i, d j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (x V : R3) :
    fderiv ℝ (fun y => referenceFiberCovectorPair g hg L lam y
      (fun i => finitePolynomialField (fun j => b j i) c y)
      (fun i => finitePolynomialField (fun j => d j i) z y)) x V =
      referenceFiberCovectorPair g hg L lam x
        (referenceCovectorPolynomialDerivative g L lam b c x V)
        (fun i => finitePolynomialField (fun j => d j i) z x) +
      referenceFiberCovectorPair g hg L lam x
        (fun i => finitePolynomialField (fun j => b j i) c x)
        (referenceCovectorPolynomialDerivative g L lam d z x V) := by
  have heq : (fun y => referenceFiberCovectorPair g hg L lam y
      (fun i => finitePolynomialField (fun j => b j i) c y)
      (fun i => finitePolynomialField (fun j => d j i) z y)) =
      fun y => (sphereNormalization 3 k)⁻¹ * finiteCovectorFischerPair b d c z y := by
    funext y
    rw [referenceFiberCovectorPair_finite hF g hg L lam k b d hb hd c z]
    simp only [div_eq_mul_inv,mul_comm]
  rw [heq,fderiv_const_mul ((contDiff_finiteCovectorFischerPair b d c z hc hz).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [fderiv_finiteCovectorFischerPair g hg L lam b d c z hc hz]
  rw [referenceFiberCovectorPair_eq hF g hg L lam x k _ _
      (fun i => referenceCovectorPolynomialDerivative_harmonicHomogeneous g hg L lam k hk b hb c x V i)
      (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hd j i) z x),
    referenceFiberCovectorPair_eq hF g hg L lam x k _ _
      (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hb j i) c x)
      (fun i => referenceCovectorPolynomialDerivative_harmonicHomogeneous g hg L lam k hk d hd z x V i)]
  rw [Finset.sum_add_distrib]
  ring

theorem compact_referenceFiberCovectorPair_contraction (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (rho : R3 → ℝ) (hr : ContDiff ℝ ∞ rho) (V : R3 → R3) (hV : ContDiff ℝ ∞ V)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (d : κ → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hb : ∀ j i, b j i ∈ harmonicHomogeneous k) (hd : ∀ j i, d j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z)
    (hcompact : HasCompactSupport c) :
    (∫ x : R3, rho x *
      (referenceFiberCovectorPair g hg L lam x
        (referenceCovectorPolynomialDerivative g L lam b c x (V x))
        (fun i => finitePolynomialField (fun j => d j i) z x) +
      referenceFiberCovectorPair g hg L lam x
        (fun i => finitePolynomialField (fun j => b j i) c x)
        (referenceCovectorPolynomialDerivative g L lam d z x (V x)))) =
      -(∫ x : R3, weightedCoordinateDivergence rho V x * referenceFiberCovectorPair g hg L lam x
        (fun i => finitePolynomialField (fun j => b j i) c x)
        (fun i => finitePolynomialField (fun j => d j i) z x)) := by
  have h := compact_weighted_scalar_variable_adjoint rho _ V hr
    (contDiff_referenceFiberCovectorPair_finite hF g hg L lam k b d hb hd c z hc hz) hV
    (hasCompactSupport_referenceFiberCovectorPair_finite hF g hg L lam k b d hb hd c z hcompact)
  simpa only [fderiv_referenceFiberCovectorPair_finite hF g hg L lam k hk b d hb hd c z hc hz] using h

end OAI.AnisotropicCalderon.MetricFiberCovectorTransport
