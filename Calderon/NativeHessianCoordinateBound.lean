import Calderon.NativeHarmonicBulkDerivativeMoments
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.NativeHessianCoordinateBound
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma norm_sq_linearMap_le_coordinate_squares (T : R3 →L[ℝ] R3) :
    ‖T‖^2 ≤ ∑ j : Fin 3, ∑ i : Fin 3,
      ((T (EuclideanSpace.single i 1)) j)^2 := by
  let row (j : Fin 3) : R3 →L[ℝ] ℝ := (EuclideanSpace.proj j).comp T
  let S : ℝ := ∑ j : Fin 3, ‖row j‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => sq_nonneg ‖row j‖)
  have hPoint (v : R3) : ‖T v‖^2 ≤ S*‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin 3, (row j v)^2) ≤ S*‖v‖^2
    calc
      (∑ j : Fin 3, (row j v)^2) ≤
          ∑ j : Fin 3, ‖row j‖^2*‖v‖^2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := pow_le_pow_left₀ (norm_nonneg (row j v)) ((row j).le_opNorm v) 2
        simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
      _ = S*‖v‖^2 := by rw [Finset.sum_mul]
  have hT : ‖T‖ ≤ Real.sqrt S := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg S)
    intro v
    have h := hPoint v
    have hs : (Real.sqrt S * ‖v‖)^2 = S*‖v‖^2 := by
      rw [mul_pow, Real.sq_sqrt hS]
    have hb : 0 ≤ Real.sqrt S * ‖v‖ := mul_nonneg (Real.sqrt_nonneg S) (norm_nonneg v)
    nlinarith [norm_nonneg (T v)]
  have hsq : ‖T‖^2 ≤ S := by
    have h := pow_le_pow_left₀ (norm_nonneg T) hT 2
    simpa only [Real.sq_sqrt hS] using h
  calc
    ‖T‖^2 ≤ S := hsq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have h := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual (row j)
      simpa only [row, EuclideanSpace.basisFun_apply,
        ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] using h

lemma fderiv_polynomial_gradient_coordinate (p : MvPolynomial (Fin 3) ℝ)
    (x : R3) (i j : Fin 3) :
    (fderiv ℝ (gradient (smoothPolynomialData p).1) x (EuclideanSpace.single i 1)) j =
      (pderiv i (pderiv j p)).eval (fun k => x k) := by
  have hg : DifferentiableAt ℝ (gradient (smoothPolynomialData p).1) x :=
    ((smoothPolynomialData p).2.gradient_right (m := ∞) (by simp)).differentiable (by simp) x
  have heq : (fun y : R3 => (gradient (smoothPolynomialData p).1 y) j) =
      fun y : R3 => (pderiv j p).eval (polynomialCoordinateMap y) := by
    funext y
    rw [← energyGradient_eq_gradient]
    exact polynomial_energyGradient_coordinate p y j
  have hd := (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt).comp x hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (gradient (smoothPolynomialData p).1 y) j) x =
    (EuclideanSpace.proj j).comp (fderiv ℝ (gradient (smoothPolynomialData p).1) x) at hd
  rw [heq] at hd
  have h := congrArg (fun L : R3 →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
  rw [← coordinateVector, fderiv_polynomialEval_coordinate] at h
  exact h.symm

lemma norm_sq_polynomial_iteratedGradient_le (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2 ≤
      ∑ j : Fin 3, ∑ i : Fin 3,
        ((pderiv i (pderiv j p)).eval (fun k => x k))^2 := by
  change ‖fderiv ℝ (gradient (smoothPolynomialData p).1) x‖^2 ≤ _
  have h := norm_sq_linearMap_le_coordinate_squares
    (fderiv ℝ (gradient (smoothPolynomialData p).1) x)
  simpa only [fderiv_polynomial_gradient_coordinate] using h

lemma integral_polynomial_iteratedGradient_square_le (hF : SphereFischerInner) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous (m+2)) :
    (∫ x in Metric.ball (0 : R3) 1,
      ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 1 x‖^2) ≤
      sphereSurfaceMass * ((m:ℝ)+2)*((m:ℝ)+1)*(2*(m:ℝ)+5)*
        ‖polynomialSphereL2 p‖^2 := by
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
      exact sum_integral_polynomial_hessian_square hF m p hp

#print axioms norm_sq_linearMap_le_coordinate_squares
#print axioms fderiv_polynomial_gradient_coordinate
#print axioms norm_sq_polynomial_iteratedGradient_le
#print axioms integral_polynomial_iteratedGradient_square_le
end OAI.AnisotropicCalderon.NativeHessianCoordinateBound
