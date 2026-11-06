import Calderon.NativeHarmonicThirdDerivativeMoments
import Calderon.NativeHarmonicH3CoordinateBound

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeFiniteHarmonicH3Bound
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  NativeFiniteHarmonicH2Bound NativeHarmonicFiniteBulkSquares NativePolynomialH2Graph
  NativeHarmonicThirdDerivativeMoments NativeHarmonicH3CoordinateBound
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma lowerOrder_polynomialBallSobolev_three (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.lowerOrder 2 (polynomialBallSobolev 3 p) = polynomialBallSobolev 2 p := by
  exact lowerOrder_smoothBallSobolev 2 (smoothPolynomialData p)

lemma norm_sq_polynomialBallSobolev_three (p : MvPolynomial (Fin 3) ℝ) :
    ‖polynomialBallSobolev 3 p‖^2 = ‖polynomialBallSobolev 2 p‖^2 +
      ∫ x in Metric.ball (0 : R3) 1,
        ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 2 x‖^2 := by
  rw [TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 1,
    lowerOrder_polynomialBallSobolev_three]
  congr 1
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [iteratedGradient_smoothBallSobolev_ae 2 (smoothPolynomialData p)] with x hx
  change ‖TauCeti.Wkp.iteratedGradient 2 (smoothBallSobolev 3 (smoothPolynomialData p)) x‖^2 = _
  rw [hx]

lemma integral_polynomial_thirdGradient_le_coordinate_integrals
    (p : MvPolynomial (Fin 3) ℝ) :
    (∫ x in Metric.ball (0 : R3) 1,
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 2 x‖^2) ≤
      3 * ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
        ∫ x in Metric.ball (0 : R3) 1,
          ((pderiv a (pderiv b (pderiv c p))).eval (fun t => x t))^2 := by
  have hSmooth : ContDiff ℝ ∞
      (fun x => fderiv ℝ (fun y => fderiv ℝ (gradient (smoothPolynomialData p).1) y) x) :=
    (((smoothPolynomialData p).2.gradient_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hc : Continuous (fun x : R3 =>
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 2 x‖^2) :=
    hSmooth.continuous.norm.pow 2
  have hInt : IntegrableOn (fun x : R3 =>
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 2 x‖^2)
      (Metric.ball (0 : R3) 1) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)).mono_set
      Metric.ball_subset_closedBall
  have hCoord (a c b : Fin 3) :=
    integrableOn_polynomial_square_ball (pderiv a (pderiv b (pderiv c p)))
  have hSum : IntegrableOn (fun x : R3 => ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
      ((pderiv a (pderiv b (pderiv c p))).eval (fun t => x t))^2)
      (Metric.ball (0 : R3) 1) :=
    integrable_finsetSum Finset.univ fun a _ =>
      integrable_finsetSum Finset.univ fun c _ =>
        integrable_finsetSum Finset.univ fun b _ => hCoord a c b
  calc
    _ ≤ ∫ x in Metric.ball (0 : R3) 1,
        3 * ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
          ((pderiv a (pderiv b (pderiv c p))).eval (fun t => x t))^2 :=
      integral_mono_ae hInt (hSum.const_mul 3)
        (Filter.Eventually.of_forall (norm_sq_polynomial_thirdGradient_le p))
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun a _ =>
        integrable_finsetSum Finset.univ (fun c _ =>
          integrable_finsetSum Finset.univ (fun b _ => hCoord a c b)))]
      simp_rw [integral_finsetSum Finset.univ (fun c _ =>
        integrable_finsetSum Finset.univ (fun b _ => hCoord _ c b)),
        integral_finsetSum Finset.univ (fun b _ => hCoord _ _ b)]

lemma sum_integral_third_derivative_finite_harmonics
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    (∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv a (pderiv b (pderiv c (∑ k ∈ s, p k)))).eval (fun t => x t))^2) =
    ∑ k ∈ s, sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*
      (2*(k:ℝ)-1)*(2*(k:ℝ)+1)*‖polynomialSphereL2 (p k)‖^2 := by
  classical
  have hLocal (k : ℕ) (hk : k ∈ s) :
      (∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2) =
      sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*
        (2*(k:ℝ)-1)*(2*(k:ℝ)+1)*‖polynomialSphereL2 (p k)‖^2 := by
    calc
      _ = ∑ c : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
          ∫ x in Metric.ball (0 : R3) 1,
            ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2 :=
        Finset.sum_comm
      _ = ∑ c : Fin 3, ∑ b : Fin 3, ∑ a : Fin 3,
          ∫ x in Metric.ball (0 : R3) 1,
            ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2 := by
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = _ := sum_integral_polynomial_third_derivative_square_all hF k (p k) (hp k hk)
  simp_rw [integral_harmonic_third_derivative_sum_square_eq_sum hO s p hp]
  calc
    _ = ∑ a : Fin 3, ∑ c : Fin 3, ∑ k ∈ s, ∑ b : Fin 3,
        ∫ x in Metric.ball (0 : R3) 1,
          ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ a : Fin 3, ∑ k ∈ s, ∑ c : Fin 3, ∑ b : Fin 3,
        ∫ x in Metric.ball (0 : R3) 1,
          ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
        ∫ x in Metric.ball (0 : R3) 1,
          ((pderiv a (pderiv b (pderiv c (p k)))).eval (fun t => x t))^2 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl hLocal

lemma harmonic_H3_weight_le (k : ℕ) :
    3*(1+(k:ℝ))^3 +
      3*(k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*(2*(k:ℝ)-1)*(2*(k:ℝ)+1) ≤
        64*(1+(k:ℝ))^5 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  nlinarith [pow_nonneg hk 3,pow_nonneg hk 4,pow_nonneg hk 5,sq_nonneg (k:ℝ)]

lemma norm_sq_finite_harmonic_polynomialBallSobolev_three_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    ‖polynomialBallSobolev 3 (∑ k ∈ s, p k)‖^2 ≤
      64*sphereSurfaceMass * ∑ k ∈ s, (1+(k:ℝ))^5*‖polynomialSphereL2 (p k)‖^2 := by
  have hLow := norm_sq_finite_harmonic_polynomialBallSobolev_two_le hF hO s p hp
  have hHigh := integral_polynomial_thirdGradient_le_coordinate_integrals (∑ k ∈ s,p k)
  rw [sum_integral_third_derivative_finite_harmonics hF hO s p hp] at hHigh
  have hM : 0 ≤ sphereSurfaceMass := by unfold sphereSurfaceMass; exact ENNReal.toReal_nonneg
  calc
    _ = ‖polynomialBallSobolev 2 (∑ k ∈ s,p k)‖^2 +
        ∫ x in Metric.ball (0 : R3) 1,
          ‖TauCeti.iteratedGradientChain (smoothPolynomialData (∑ k ∈ s,p k)).1 2 x‖^2 :=
      norm_sq_polynomialBallSobolev_three _
    _ ≤ 3*sphereSurfaceMass * ∑ k ∈ s, (1+(k:ℝ))^3*‖polynomialSphereL2 (p k)‖^2 +
        3*(∑ k ∈ s, sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*
          (2*(k:ℝ)-1)*(2*(k:ℝ)+1)*‖polynomialSphereL2 (p k)‖^2) := add_le_add hLow hHigh
    _ = ∑ k ∈ s, sphereSurfaceMass *
        (3*(1+(k:ℝ))^3 + 3*(k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*(2*(k:ℝ)-1)*(2*(k:ℝ)+1))*
          ‖polynomialSphereL2 (p k)‖^2 := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k ∈ s, (64*sphereSurfaceMass) *
        ((1+(k:ℝ))^5*‖polynomialSphereL2 (p k)‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harmonic_H3_weight_le k) hM)
        (sq_nonneg ‖polynomialSphereL2 (p k)‖)
      simpa only [mul_assoc,mul_left_comm,mul_comm] using h
    _ = _ := by rw [Finset.mul_sum]

end OAI.AnisotropicCalderon.NativeFiniteHarmonicH3Bound
