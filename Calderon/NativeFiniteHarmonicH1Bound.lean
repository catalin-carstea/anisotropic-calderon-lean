import Calderon.NativeFiniteHarmonicH2Bound

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeFiniteHarmonicH1Bound
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  NativeHarmonicFiniteBulkSquares NativeFiniteHarmonicH2Bound
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma norm_sq_finite_harmonic_smoothSobolev
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    ‖smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k))‖^2 =
      sphereSurfaceMass * ∑ k ∈ s,
        (1/(2*(k:ℝ)+3)+(k:ℝ)) * ‖polynomialSphereL2 (p k)‖^2 := by
  classical
  rw [norm_smoothSobolev_sq_eq_graph_integrals]
  change (∫ x in Metric.ball (0 : R3) 1, ((∑ k ∈ s, p k).eval (fun i => x i))^2) +
    (∫ x in Metric.ball (0 : R3) 1,
      ‖energyGradient (smoothPolynomialData (∑ k ∈ s, p k)).1 x‖^2) = _
  rw [integral_harmonic_sum_square_eq_sum hO s p hp]
  simp_rw [EuclideanSpace.real_norm_sq_eq, polynomial_energyGradient_coordinate]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrableOn_polynomial_square_ball (pderiv i (∑ k ∈ s, p k)))]
  simp_rw [integral_harmonic_first_derivative_sum_square_eq_sum hO s p hp]
  rw [Finset.sum_comm,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_ball_polynomial_square (hp k hk).1,
    sum_integral_polynomial_gradient_square_all hF k (p k) (hp k hk)]
  ring

lemma harmonic_H1_weight_bounds (k : ℕ) :
    (1+(k:ℝ))/3 ≤ 1/(2*(k:ℝ)+3)+(k:ℝ) ∧
      1/(2*(k:ℝ)+3)+(k:ℝ) ≤ 1+(k:ℝ) := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hd : 0 < 2*(k:ℝ)+3 := by positivity
  constructor
  · cases k with
    | zero => norm_num
    | succ n =>
      have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      have hf : 0 ≤ 1/(2*((n+1:ℕ):ℝ)+3) := by positivity
      push_cast at *
      linarith
  · have hf := (div_le_one hd).mpr (show (1:ℝ) ≤ 2*(k:ℝ)+3 by linarith)
    linarith

lemma norm_sq_finite_harmonic_smoothSobolev_bounds
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    (sphereSurfaceMass/3) * ∑ k ∈ s, (1+(k:ℝ))*‖polynomialSphereL2 (p k)‖^2 ≤
      ‖smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k))‖^2 ∧
    ‖smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k))‖^2 ≤
      sphereSurfaceMass * ∑ k ∈ s, (1+(k:ℝ))*‖polynomialSphereL2 (p k)‖^2 := by
  classical
  rw [norm_sq_finite_harmonic_smoothSobolev hF hO s p hp]
  have hM : 0 ≤ sphereSurfaceMass := ENNReal.toReal_nonneg
  constructor
  · have h : (∑ k ∈ s, ((1+(k:ℝ))/3)*‖polynomialSphereL2 (p k)‖^2) ≤
        ∑ k ∈ s, (1/(2*(k:ℝ)+3)+(k:ℝ))*‖polynomialSphereL2 (p k)‖^2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (harmonic_H1_weight_bounds k).1 (sq_nonneg _)
    calc
      _ = sphereSurfaceMass * ∑ k ∈ s, ((1+(k:ℝ))/3)*‖polynomialSphereL2 (p k)‖^2 := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hM
  · apply mul_le_mul_of_nonneg_left _ hM
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (harmonic_H1_weight_bounds k).2 (sq_nonneg _)

#print axioms norm_sq_finite_harmonic_smoothSobolev
#print axioms harmonic_H1_weight_bounds
#print axioms norm_sq_finite_harmonic_smoothSobolev_bounds
end OAI.AnisotropicCalderon.NativeFiniteHarmonicH1Bound
