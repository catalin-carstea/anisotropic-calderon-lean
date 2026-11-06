import Calderon.NativePolynomialH2Graph
import Calderon.NativeHarmonicFiniteBulkSquares

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeFiniteHarmonicH2Bound
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  NativeHessianCoordinateBound NativePolynomialH2Graph NativeHarmonicFiniteBulkSquares
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma sum_integral_polynomial_gradient_square_all (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv i p).eval (fun j => x j))^2) =
      sphereSurfaceMass * (k:ℝ) * ‖polynomialSphereL2 p‖^2 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1]
  | succ m =>
      simpa only [Nat.cast_succ] using sum_integral_polynomial_gradient_square hF m p hp

lemma sum_integral_polynomial_hessian_square_all (hF : SphereFischerInner) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv j (pderiv i p)).eval (fun a => x a))^2) =
      sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*(2*(k:ℝ)+1)*‖polynomialSphereL2 p‖^2 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1]
  | succ k =>
      cases k with
      | zero => simp [pderiv_pderiv_eq_zero_of_harmonic_one p hp]
      | succ m =>
          have h := sum_integral_polynomial_hessian_square hF m p hp
          convert h using 1 <;> push_cast <;> ring

lemma integral_polynomial_highest_derivative_le_coordinate_integrals
    (p : MvPolynomial (Fin 3) ℝ) :
    (∫ x in Metric.ball (0 : R3) 1,
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2) ≤
      ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i (pderiv j p)).eval (fun k => x k))^2 := by
  have hc : Continuous (fun x : R3 =>
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2) := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ (gradient (smoothPolynomialData p).1)) :=
      ((smoothPolynomialData p).2.gradient_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
    exact hd.continuous.norm.pow 2
  have hInt : IntegrableOn (fun x : R3 =>
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2)
      (Metric.ball (0 : R3) 1) := (hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : R3) 1)).mono_set Metric.ball_subset_closedBall
  have hCoord (j i : Fin 3) := integrableOn_polynomial_square_ball (pderiv i (pderiv j p))
  have hSum : IntegrableOn (fun x : R3 => ∑ j : Fin 3, ∑ i : Fin 3,
      ((pderiv i (pderiv j p)).eval (fun k => x k))^2) (Metric.ball (0 : R3) 1) :=
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun i _ => hCoord j i))
  calc
    _ ≤ ∫ x in Metric.ball (0 : R3) 1, ∑ j : Fin 3, ∑ i : Fin 3,
        ((pderiv i (pderiv j p)).eval (fun k => x k))^2 :=
      integral_mono_ae hInt hSum (Filter.Eventually.of_forall
        (norm_sq_polynomial_iteratedGradient_le p))
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun i _ => hCoord j i))]
      simp_rw [integral_finsetSum Finset.univ (fun i _ => hCoord _ i)]

lemma norm_sq_polynomialBallSobolev_two_le_coordinate_integrals
    (p : MvPolynomial (Fin 3) ℝ) :
    ‖polynomialBallSobolev 2 p‖^2 ≤
      (∫ x in Metric.ball (0 : R3) 1, (p.eval (fun i => x i))^2) +
      (∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i p).eval (fun j => x j))^2) +
      (∑ j : Fin 3, ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i (pderiv j p)).eval (fun k => x k))^2) := by
  rw [norm_sq_polynomialBallSobolev_two]
  have hGrad : (∫ x in Metric.ball (0 : R3) 1,
      ‖energyGradient (smoothPolynomialData p).1 x‖^2) =
      ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i p).eval (fun j => x j))^2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq, polynomial_energyGradient_coordinate]
    rw [integral_finsetSum Finset.univ (fun i _ => integrableOn_polynomial_square_ball (pderiv i p))]
  rw [hGrad]
  exact add_le_add (le_refl _) (integral_polynomial_highest_derivative_le_coordinate_integrals p)

lemma harmonic_H2_weight_le (k : ℕ) :
    1/(2*(k:ℝ)+3) + (k:ℝ) + (k:ℝ)*((k:ℝ)-1)*(2*(k:ℝ)+1) ≤
      3*(1+(k:ℝ))^3 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hd : 0 < 2*(k:ℝ)+3 := by positivity
  have hf : 1/(2*(k:ℝ)+3) ≤ 1 := (div_le_one hd).mpr (by linarith)
  nlinarith [mul_nonneg hk (sq_nonneg (k:ℝ))]

lemma norm_sq_finite_harmonic_polynomialBallSobolev_two_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    ‖polynomialBallSobolev 2 (∑ k ∈ s, p k)‖^2 ≤
      3*sphereSurfaceMass * ∑ k ∈ s, (1+(k:ℝ))^3 * ‖polynomialSphereL2 (p k)‖^2 := by
  classical
  have hV : (∫ x in Metric.ball (0 : R3) 1,
      ((∑ k ∈ s, p k).eval (fun i => x i))^2) =
      ∑ k ∈ s, sphereSurfaceMass / (2*(k:ℝ)+3) * ‖polynomialSphereL2 (p k)‖^2 := by
    rw [integral_harmonic_sum_square_eq_sum hO s p hp]
    apply Finset.sum_congr rfl
    intro k hk
    exact integral_ball_polynomial_square (hp k hk).1
  have hG : (∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv i (∑ k ∈ s, p k)).eval (fun j => x j))^2) =
      ∑ k ∈ s, sphereSurfaceMass * (k:ℝ)*‖polynomialSphereL2 (p k)‖^2 := by
    simp_rw [integral_harmonic_first_derivative_sum_square_eq_sum hO s p hp]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact sum_integral_polynomial_gradient_square_all hF k (p k) (hp k hk)
  have hH : (∑ j : Fin 3, ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv i (pderiv j (∑ k ∈ s, p k))).eval (fun a => x a))^2) =
      ∑ k ∈ s, sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*(2*(k:ℝ)+1)*
        ‖polynomialSphereL2 (p k)‖^2 := by
    simp_rw [integral_harmonic_second_derivative_sum_square_eq_sum hO s p hp]
    calc
      (∑ j : Fin 3, ∑ i : Fin 3, ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i (pderiv j (p k))).eval (fun a => x a))^2) =
          ∑ j : Fin 3, ∑ k ∈ s, ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
            ((pderiv i (pderiv j (p k))).eval (fun a => x a))^2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
      _ = ∑ k ∈ s, ∑ j : Fin 3, ∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
          ((pderiv i (pderiv j (p k))).eval (fun a => x a))^2 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_integral_polynomial_hessian_square_all hF k (p k) (hp k hk)
  have hM : 0 ≤ sphereSurfaceMass := by
    unfold sphereSurfaceMass
    exact ENNReal.toReal_nonneg
  calc
    ‖polynomialBallSobolev 2 (∑ k ∈ s, p k)‖^2 ≤ _ :=
      norm_sq_polynomialBallSobolev_two_le_coordinate_integrals (∑ k ∈ s, p k)
    _ = ∑ k ∈ s, sphereSurfaceMass *
        (1/(2*(k:ℝ)+3)+(k:ℝ)+(k:ℝ)*((k:ℝ)-1)*(2*(k:ℝ)+1)) *
          ‖polynomialSphereL2 (p k)‖^2 := by
      rw [hV,hG,hH,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k ∈ s, (3*sphereSurfaceMass) *
        ((1+(k:ℝ))^3 * ‖polynomialSphereL2 (p k)‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harmonic_H2_weight_le k) hM)
        (sq_nonneg ‖polynomialSphereL2 (p k)‖)
      simpa only [mul_assoc,mul_left_comm,mul_comm] using h
    _ = _ := by rw [Finset.mul_sum]

#print axioms sum_integral_polynomial_gradient_square_all
#print axioms sum_integral_polynomial_hessian_square_all
#print axioms integral_polynomial_highest_derivative_le_coordinate_integrals
#print axioms norm_sq_polynomialBallSobolev_two_le_coordinate_integrals
#print axioms harmonic_H2_weight_le
#print axioms norm_sq_finite_harmonic_polynomialBallSobolev_two_le
end OAI.AnisotropicCalderon.NativeFiniteHarmonicH2Bound
