import Calderon.NativeHarmonicBulkDerivativeMoments

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeHarmonicFiniteBulkSquares
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  SphereHarmonic DirichletFamily

lemma pderiv_eq_zero_of_homogeneous_zero (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous 0) (i : Fin 3) : pderiv i p = 0 := by
  have hd : p.totalDegree = 0 := Nat.eq_zero_of_le_zero hp.totalDegree_le
  have h := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  rw [h, pderiv_C]

lemma integral_first_derivative_cross_eq_zero (hO : OrthogonalSphereHarmonics)
    (k l : ℕ) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous l)
    (hkl : k ≠ l) (i j : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      (pderiv i p).eval (fun a => x a) * (pderiv j q).eval (fun a => x a)) = 0 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1 i]
  | succ k =>
      cases l with
      | zero => simp [pderiv_eq_zero_of_homogeneous_zero q hq.1 j]
      | succ l =>
          exact integral_polynomial_first_derivative_orthogonal hO k l p q hp hq
            (fun h => hkl (congrArg Nat.succ h)) i j

lemma pderiv_pderiv_eq_zero_of_harmonic_one (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous 1) (i j : Fin 3) : pderiv j (pderiv i p) = 0 := by
  exact pderiv_eq_zero_of_homogeneous_zero (pderiv i p)
    (pderiv_harmonicHomogeneous_succ 0 i p hp).1 j

lemma integral_second_derivative_cross_eq_zero (hO : OrthogonalSphereHarmonics)
    (k l : ℕ) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous l)
    (hkl : k ≠ l) (i j a b : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      (pderiv j (pderiv i p)).eval (fun c => x c) *
      (pderiv b (pderiv a q)).eval (fun c => x c)) = 0 := by
  cases k with
  | zero => simp [pderiv_eq_zero_of_homogeneous_zero p hp.1 i]
  | succ k =>
      cases k with
      | zero => simp [pderiv_pderiv_eq_zero_of_harmonic_one p hp i j]
      | succ k =>
          cases l with
          | zero => simp [pderiv_eq_zero_of_homogeneous_zero q hq.1 a]
          | succ l =>
              cases l with
              | zero => simp [pderiv_pderiv_eq_zero_of_harmonic_one q hq a b]
              | succ l =>
                  exact integral_polynomial_second_derivative_orthogonal hO k l p q hp hq
                    (fun h => hkl (congrArg (fun n => n+2) h)) i j a b

lemma integrableOn_polynomial_product_ball (p q : MvPolynomial (Fin 3) ℝ) :
    IntegrableOn (fun x : R3 => p.eval (fun i => x i) * q.eval (fun i => x i))
      (Metric.ball (0 : R3) 1) := by
  have hc : Continuous (fun x : R3 => p.eval (fun i => x i) * q.eval (fun i => x i)) :=
    (contDiff_polynomialEval p).continuous.mul (contDiff_polynomialEval q).continuous
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) 1)).mono_set
    Metric.ball_subset_closedBall

lemma integral_polynomial_sum_square_eq_sum (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hOrth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l →
      (∫ x in Metric.ball (0 : R3) 1,
        (p k).eval (fun i => x i) * (p l).eval (fun i => x i)) = 0) :
    (∫ x in Metric.ball (0 : R3) 1, ((∑ k ∈ s, p k).eval (fun i => x i))^2) =
      ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1, ((p k).eval (fun i => x i))^2 := by
  classical
  simp_rw [map_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum s (fun k _ => integrable_finsetSum s
    (fun l _ => integrableOn_polynomial_product_ball (p k) (p l)))]
  simp_rw [integral_finsetSum s (fun l _ => integrableOn_polynomial_product_ball (p _) (p l))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single k]
  · intro l hl hlk
    exact hOrth k hk l hl hlk.symm
  · intro h
    exact False.elim (h hk)

lemma integral_harmonic_sum_square_eq_sum (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    (∫ x in Metric.ball (0 : R3) 1, ((∑ k ∈ s, p k).eval (fun i => x i))^2) =
      ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1, ((p k).eval (fun i => x i))^2 := by
  apply integral_polynomial_sum_square_eq_sum
  intro k hk l hl hkl
  exact integral_ball_harmonic_orthogonal hO (hp k hk) (hp l hl) hkl

lemma integral_harmonic_first_derivative_sum_square_eq_sum (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) (i : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      ((pderiv i (∑ k ∈ s, p k)).eval (fun j => x j))^2) =
      ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv i (p k)).eval (fun j => x j))^2 := by
  rw [map_sum]
  apply integral_polynomial_sum_square_eq_sum
  intro k hk l hl hkl
  exact integral_first_derivative_cross_eq_zero hO k l (p k) (p l) (hp k hk) (hp l hl) hkl i i

lemma integral_harmonic_second_derivative_sum_square_eq_sum (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) (i j : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      ((pderiv j (pderiv i (∑ k ∈ s, p k))).eval (fun a => x a))^2) =
      ∑ k ∈ s, ∫ x in Metric.ball (0 : R3) 1,
        ((pderiv j (pderiv i (p k))).eval (fun a => x a))^2 := by
  rw [map_sum, map_sum]
  apply integral_polynomial_sum_square_eq_sum
  intro k hk l hl hkl
  exact integral_second_derivative_cross_eq_zero hO k l (p k) (p l) (hp k hk) (hp l hl) hkl i j i j

#print axioms pderiv_eq_zero_of_homogeneous_zero
#print axioms integral_first_derivative_cross_eq_zero
#print axioms pderiv_pderiv_eq_zero_of_harmonic_one
#print axioms integral_second_derivative_cross_eq_zero
#print axioms integrableOn_polynomial_product_ball
#print axioms integral_polynomial_sum_square_eq_sum
#print axioms integral_harmonic_sum_square_eq_sum
#print axioms integral_harmonic_first_derivative_sum_square_eq_sum
#print axioms integral_harmonic_second_derivative_sum_square_eq_sum
end OAI.AnisotropicCalderon.NativeHarmonicFiniteBulkSquares
