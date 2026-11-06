import Calderon.LiteratureGaussianSphere
import Calderon.LiteratureGaussianFischer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Sphere integrals of products of harmonic polynomials, from the Gaussian pairing
(helper for tasks 01 and 03). -/

noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

theorem eval_smul_of_isHomogeneous {p : MvPolynomial (Fin 3) ℝ} {k : ℕ} (hp : p.IsHomogeneous k)
    (t : ℝ) (x : Fin 3 → ℝ) : eval (t • x) p = t ^ k * eval x p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = k := by
    have := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The pointwise product `p q` on `R3`. -/
def pq (p q : MvPolynomial (Fin 3) ℝ) (x : R3) : ℝ :=
  p.eval (x : Fin 3 → ℝ) * q.eval (x : Fin 3 → ℝ)

theorem continuous_pq (p q : MvPolynomial (Fin 3) ℝ) : Continuous (pq p q) := by
  unfold pq
  exact (p.continuous_eval.comp (PiLp.continuous_ofLp 2 _)).mul
    (q.continuous_eval.comp (PiLp.continuous_ofLp 2 _))

theorem pq_smul {p q : MvPolynomial (Fin 3) ℝ} {k m : ℕ} (hp : p.IsHomogeneous k)
    (hq : q.IsHomogeneous m) (t : ℝ) (x : R3) : pq p q (t • x) = t ^ (k + m) * pq p q x := by
  simp only [pq, WithLp.ofLp_smul, eval_smul_of_isHomogeneous hp, eval_smul_of_isHomogeneous hq]
  ring

/-- The Gaussian pairing in terms of the sphere integral. -/
theorem gaussPair_eq_sphere {p q : MvPolynomial (Fin 3) ℝ} {k m : ℕ} (hp : p.IsHomogeneous k)
    (hq : q.IsHomogeneous m) :
    gaussPair p q = (∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure) *
      (Real.Gamma ((((k + m : ℕ) : ℝ) + 3) / 2) / 2) := by
  have := integral_mul_gaussian_of_homogeneous (continuous_pq p q) (k + m)
    (fun t x _ => pq_smul hp hq t x)
  rw [← this]
  rfl

theorem sphereInner_eq (p q : MvPolynomial (Fin 3) ℝ) :
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ =
      (surfaceMeasure Set.univ).toReal⁻¹ * ∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure := by
  rw [polynomialSphereL2_inner, sphereProbability, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_inv]
  rfl


theorem one_mem_harmonicHomogeneous : (1 : MvPolynomial (Fin 3) ℝ) ∈ harmonicHomogeneous 0 :=
  ⟨isHomogeneous_one _ _, by simp [laplacian]⟩

theorem fischerInner_one_one : fischerInner (1 : MvPolynomial (Fin 3) ℝ) 1 = 1 := by
  simp [fischerInner, fischerWeight, MvPolynomial.coeff_one]

/-- `σ(S²) Γ(3/2) / 2 = π^{3/2}`. -/
theorem surface_mul_gamma :
    (surfaceMeasure Set.univ).toReal * (Real.Gamma (3 / 2) / 2) = Real.pi ^ ((3 : ℝ) / 2) := by
  have h1 := gaussPair_eq_fischer one_mem_harmonicHomogeneous one_mem_harmonicHomogeneous
  have h2 := gaussPair_eq_sphere (isHomogeneous_one (Fin 3) ℝ) (isHomogeneous_one (Fin 3) ℝ)
  rw [h2, fischerInner_one_one] at h1
  have hS : ∫ ω : UnitSphere, pq 1 1 ω ∂surfaceMeasure = (surfaceMeasure Set.univ).toReal := by
    simp [pq, Measure.real]
  rw [hS] at h1
  simpa using h1

theorem gamma_half_odd (k : ℕ) :
    Real.Gamma ((((k + k : ℕ) : ℝ) + 3) / 2) =
      Real.Gamma (3 / 2) * (sphereNormalization 3 k / 2 ^ k) := by
  induction k with
  | zero => norm_num [sphereNormalization]
  | succ k ih =>
      have harg : (((k + 1 + (k + 1) : ℕ) : ℝ) + 3) / 2 = ((((k + k : ℕ) : ℝ) + 3) / 2) + 1 := by
        push_cast; ring
      rw [harg, Real.Gamma_add_one (by positivity), ih]
      simp only [sphereNormalization, Finset.prod_range_succ, pow_succ]
      push_cast
      field_simp
      ring

end OAI.AnisotropicCalderon.SphereHarmonic
