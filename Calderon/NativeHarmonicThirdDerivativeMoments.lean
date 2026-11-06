import Calderon.NativeFiniteHarmonicH2Bound

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeHarmonicThirdDerivativeMoments
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  NativeFiniteHarmonicH2Bound NativeHarmonicFiniteBulkSquares HarmonicDerivativeBounds
  NativeHessianCoordinateBound SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma integral_third_derivative_cross_eq_zero
    (hO : OrthogonalSphereHarmonics) (k l : ℕ)
    (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous l)
    (hkl : k ≠ l) (i j a b c d : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      (pderiv a (pderiv j (pderiv i p))).eval (fun t => x t) *
      (pderiv d (pderiv c (pderiv b q))).eval (fun t => x t)) = 0 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1 i]
  | succ k =>
    cases l with
    | zero => simp [pderiv_eq_zero_of_homogeneous_zero q hq.1 b]
    | succ l =>
      exact integral_second_derivative_cross_eq_zero hO k l (pderiv i p) (pderiv b q)
        (pderiv_harmonicHomogeneous_succ k i p hp)
        (pderiv_harmonicHomogeneous_succ l b q hq)
        (fun h => hkl (congrArg Nat.succ h)) j a c d

lemma integral_harmonic_third_derivative_sum_square_eq_sum
    (hO : OrthogonalSphereHarmonics) (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) (i j a : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      ((pderiv a (pderiv j (pderiv i (∑ k ∈ s, p k)))).eval (fun t => x t))^2) =
    ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv a (pderiv j (pderiv i (p k)))).eval (fun t => x t))^2 := by
  rw [map_sum,map_sum,map_sum]
  apply integral_polynomial_sum_square_eq_sum
  intro k hk l hl hkl
  exact integral_third_derivative_cross_eq_zero hO k l (p k) (p l)
    (hp k hk) (hp l hl) hkl i j a i j a

lemma sum_integral_polynomial_third_derivative_square_all
    (hF : SphereFischerInner) (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ a : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv a (pderiv j (pderiv i p))).eval (fun t => x t))^2) =
    sphereSurfaceMass * (k:ℝ)*((k:ℝ)-1)*((k:ℝ)-2)*(2*(k:ℝ)-1)*(2*(k:ℝ)+1)*
      ‖polynomialSphereL2 p‖^2 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1]
  | succ m =>
    simp_rw [sum_integral_polynomial_hessian_square_all hF m (pderiv _ p)
      (pderiv_harmonicHomogeneous_succ m _ p hp)]
    rw [← Finset.mul_sum,sum_norm_sq_polynomialDerivative hF m p hp]
    push_cast
    ring

end OAI.AnisotropicCalderon.NativeHarmonicThirdDerivativeMoments
