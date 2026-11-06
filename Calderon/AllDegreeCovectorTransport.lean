import Calderon.MetricFiberCovectorTransport

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff
namespace OAI.AnisotropicCalderon.AllDegreeCovectorTransport
open AngularPolynomial SphereHarmonic MovingFrameConnection FischerConnectionTransport
  PolynomialSlotCompatibility FiniteCovectorTransport MetricFiberCovectorTransport
  FischerDensityIntegration

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma referenceCovariantPolynomialDerivative_harmonicHomogeneous_all (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ j, b j ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x V : R3) :
    referenceCovariantPolynomialDerivative g L lam b c x V ∈ harmonicHomogeneous k := by
  by_cases hk : k = 0
  · subst k
    have hhom := (finitePolynomialField_harmonicHomogeneous 0 b hb c x).1
    rw [referenceCovariantPolynomialDerivative,
      referenceFrameAngularPolynomial_eq_zero_of_isHomogeneous_zero g L lam x V _ hhom,add_zero]
    exact finitePolynomialFieldDerivative_harmonicHomogeneous 0 b hb c x V
  · exact referenceCovariantPolynomialDerivative_harmonicHomogeneous g hg L lam k
      (Nat.one_le_iff_ne_zero.mpr hk) b hb c x V

lemma referenceCovectorPolynomialDerivative_harmonicHomogeneous_all (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
    (b : ι → Fin 3 → MvPolynomial (Fin 3) ℝ) (hb : ∀ j i, b j i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x V : R3) (i : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam b c x V i ∈ harmonicHomogeneous k := by
  apply (harmonicHomogeneous k).sub_mem
    (referenceCovariantPolynomialDerivative_harmonicHomogeneous_all g hg L lam k _ (fun j => hb j i) c x V)
  apply (harmonicHomogeneous k).sum_mem
  intro a _
  simpa only [smul_eq_C_mul] using (harmonicHomogeneous k).smul_mem
    (referenceFrameConnectionCoefficient g L lam x V a i)
    (finitePolynomialField_harmonicHomogeneous k _ (fun j => hb j a) c x)

theorem fderiv_referenceFiberCovectorPair_finite_all (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
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
      (fun i => referenceCovectorPolynomialDerivative_harmonicHomogeneous_all g hg L lam k b hb c x V i)
      (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hd j i) z x),
    referenceFiberCovectorPair_eq hF g hg L lam x k _ _
      (fun i => finitePolynomialField_harmonicHomogeneous k _ (fun j => hb j i) c x)
      (fun i => referenceCovectorPolynomialDerivative_harmonicHomogeneous_all g hg L lam k d hd z x V i)]
  rw [Finset.sum_add_distrib]
  ring

theorem compact_referenceFiberCovectorPair_contraction_all (hF : SphereFischerInner) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ)
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
  simpa only [fderiv_referenceFiberCovectorPair_finite_all hF g hg L lam k b d hb hd c z hc hz] using h

end OAI.AnisotropicCalderon.AllDegreeCovectorTransport
