import Calderon.NativePolynomialBulkMoments
import Calderon.NativePolynomialBallSobolev
import Calderon.HarmonicDerivativeBounds
import Calderon.SmoothSobolevBridge
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeHarmonicBulkDerivativeMoments
open NativePolynomialBulkMoments SphereHarmonic HarmonicDerivativeBounds
  DirichletFamily EnergyBridge MetricVolume

lemma integrableOn_polynomial_square_ball (p : MvPolynomial (Fin 3) ℝ) :
    IntegrableOn (fun x : R3 => (p.eval (fun i => x i))^2)
      (Metric.ball (0 : R3) 1) := by
  have hc : Continuous (fun x : R3 => (p.eval (fun i => x i))^2) := by
    exact (contDiff_polynomialEval p).continuous.pow 2
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)).mono_set
    Metric.ball_subset_closedBall

lemma sum_integral_polynomial_gradient_square (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+1)) :
    (∑ i : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv i p).eval (fun j => x j))^2) =
      sphereSurfaceMass * ((m:ℝ)+1) * ‖polynomialSphereL2 p‖^2 := by
  simp_rw [integral_ball_polynomial_square
    (pderiv_harmonicHomogeneous_succ m _ p hp).1]
  rw [← Finset.mul_sum, sum_norm_sq_polynomialDerivative hF m p hp]
  have hd : 2*(m:ℝ)+3 ≠ 0 := by positivity
  field_simp [hd]
  <;> ring

lemma sum_sphere_polynomial_hessian_square (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+2)) :
    (∑ i : Fin 3, ∑ j : Fin 3, ‖polynomialSphereL2 (pderiv j (pderiv i p))‖^2) =
      (((m:ℝ)+1)*(2*(m:ℝ)+3)*((m:ℝ)+2)*(2*(m:ℝ)+5)) *
        ‖polynomialSphereL2 p‖^2 := by
  have hp' : p ∈ harmonicHomogeneous ((m+1)+1) := by simpa [Nat.add_assoc] using hp
  simp_rw [sum_norm_sq_polynomialDerivative hF m (pderiv _ p)
    (pderiv_harmonicHomogeneous_succ (m+1) _ p hp')]
  rw [← Finset.mul_sum, sum_norm_sq_polynomialDerivative hF (m+1) p hp']
  push_cast
  ring

lemma sum_integral_polynomial_hessian_square (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+2)) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in Metric.ball (0 : R3) 1,
      ((pderiv j (pderiv i p)).eval (fun k => x k))^2) =
      sphereSurfaceMass * ((m:ℝ)+2)*((m:ℝ)+1)*(2*(m:ℝ)+5)*
        ‖polynomialSphereL2 p‖^2 := by
  have hp' : p ∈ harmonicHomogeneous ((m+1)+1) := by simpa [Nat.add_assoc] using hp
  simp_rw [integral_ball_polynomial_square
    (pderiv_harmonicHomogeneous_succ m _ _
      (pderiv_harmonicHomogeneous_succ (m+1) _ p hp')).1]
  simp_rw [← Finset.mul_sum]
  rw [sum_sphere_polynomial_hessian_square hF m p hp]
  have hd : 2*(m:ℝ)+3 ≠ 0 := by positivity
  field_simp [hd]
  <;> ring

lemma polynomial_energyGradient_coordinate (p : MvPolynomial (Fin 3) ℝ)
    (x : R3) (i : Fin 3) :
    energyGradient (smoothPolynomialData p).1 x i = (pderiv i p).eval (fun j => x j) := by
  change fderiv ℝ (fun y : R3 => p.eval (polynomialCoordinateMap y)) x
    (EuclideanSpace.single i 1) = _
  simpa only [coordinateVector] using fderiv_polynomialEval_coordinate p x i

lemma integral_polynomial_energyGradient_square (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+1)) :
    (∫ x in Metric.ball (0 : R3) 1, ‖energyGradient (smoothPolynomialData p).1 x‖^2) =
      sphereSurfaceMass * ((m:ℝ)+1) * ‖polynomialSphereL2 p‖^2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, polynomial_energyGradient_coordinate]
  rw [integral_finsetSum Finset.univ (fun i _ => integrableOn_polynomial_square_ball (pderiv i p))]
  exact sum_integral_polynomial_gradient_square hF m p hp

lemma norm_smoothPolynomialSobolev_sq (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+1)) :
    ‖smoothSobolev (smoothPolynomialData p)‖^2 =
      sphereSurfaceMass * (1 / (2*(m:ℝ)+5) + ((m:ℝ)+1)) *
        ‖polynomialSphereL2 p‖^2 := by
  rw [norm_smoothSobolev_sq_eq_graph_integrals]
  change (∫ x in Metric.ball (0 : R3) 1, (p.eval (fun i => x i))^2) +
    (∫ x in Metric.ball (0 : R3) 1, ‖energyGradient (smoothPolynomialData p).1 x‖^2) = _
  rw [integral_ball_polynomial_square hp.1,
    integral_polynomial_energyGradient_square hF m p hp]
  push_cast
  ring

lemma integral_polynomial_first_derivative_orthogonal (hO : OrthogonalSphereHarmonics)
    (m n : ℕ) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous (m+1)) (hq : q ∈ harmonicHomogeneous (n+1))
    (hmn : m ≠ n) (i j : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      (pderiv i p).eval (fun k => x k) * (pderiv j q).eval (fun k => x k)) = 0 := by
  exact integral_ball_harmonic_orthogonal hO
    (pderiv_harmonicHomogeneous_succ m i p hp)
    (pderiv_harmonicHomogeneous_succ n j q hq) hmn

lemma integral_polynomial_second_derivative_orthogonal (hO : OrthogonalSphereHarmonics)
    (m n : ℕ) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous (m+2)) (hq : q ∈ harmonicHomogeneous (n+2))
    (hmn : m ≠ n) (i j a b : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      (pderiv j (pderiv i p)).eval (fun k => x k) *
      (pderiv b (pderiv a q)).eval (fun k => x k)) = 0 := by
  have hp' : p ∈ harmonicHomogeneous ((m+1)+1) := by simpa [Nat.add_assoc] using hp
  have hq' : q ∈ harmonicHomogeneous ((n+1)+1) := by simpa [Nat.add_assoc] using hq
  exact integral_ball_harmonic_orthogonal hO
    (pderiv_harmonicHomogeneous_succ m j _
      (pderiv_harmonicHomogeneous_succ (m+1) i p hp'))
    (pderiv_harmonicHomogeneous_succ n b _
      (pderiv_harmonicHomogeneous_succ (n+1) a q hq')) hmn

#print axioms integrableOn_polynomial_square_ball
#print axioms sum_integral_polynomial_gradient_square
#print axioms sum_sphere_polynomial_hessian_square
#print axioms sum_integral_polynomial_hessian_square
#print axioms polynomial_energyGradient_coordinate
#print axioms integral_polynomial_energyGradient_square
#print axioms norm_smoothPolynomialSobolev_sq
#print axioms integral_polynomial_first_derivative_orthogonal
#print axioms integral_polynomial_second_derivative_orthogonal
end OAI.AnisotropicCalderon.NativeHarmonicBulkDerivativeMoments
