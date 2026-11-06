import Calderon.NativeFiniteHarmonicH2Bound

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ContDiff Gradient
namespace OAI.AnisotropicCalderon.NativeHarmonicH3CoordinateBound
open NativePolynomialBulkMoments NativeHarmonicBulkDerivativeMoments
  NativeFiniteHarmonicH2Bound NativeHarmonicFiniteBulkSquares HarmonicDerivativeBounds
  NativeHessianCoordinateBound SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma norm_sq_clm_le_three_sum_coordinate_norms {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : R3 →L[ℝ] E) :
    ‖T‖^2 ≤ 3 * ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖^2 := by
  let S : ℝ := ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hT : ‖T‖ ≤ S := by
    apply T.opNorm_le_bound hS
    intro v
    have hv : v = ∑ i : Fin 3, (v i) • EuclideanSpace.single i 1 := by
      ext j
      simp [Pi.single_apply]
    have hDecomp : T v = ∑ i : Fin 3, (v i) • T (EuclideanSpace.single i 1) := by
      conv_lhs => rw [hv]
      simp only [map_sum,map_smul]
    rw [hDecomp]
    calc
      _ ≤ ∑ i : Fin 3, ‖(v i) • T (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, ‖v i‖ * ‖T (EuclideanSpace.single i 1)‖ := by simp only [norm_smul]
      _ ≤ ∑ i : Fin 3, ‖v‖ * ‖T (EuclideanSpace.single i 1)‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
      _ = S*‖v‖ := by rw [← Finset.mul_sum]; ring
  have hCS : S^2 ≤ 3 * ∑ i : Fin 3, ‖T (EuclideanSpace.single i 1)‖^2 := by
    simpa only [S,one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_ofNat,mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
        (fun _ => (1 : ℝ)) (fun i => ‖T (EuclideanSpace.single i 1)‖))
  exact (pow_le_pow_left₀ (norm_nonneg _) hT 2).trans hCS

lemma fderiv_polynomial_hessian_coordinate (p : MvPolynomial (Fin 3) ℝ)
    (x : R3) (a b c : Fin 3) :
    ((fderiv ℝ (fun y => fderiv ℝ (gradient (smoothPolynomialData p).1) y) x
      (EuclideanSpace.single a 1)) (EuclideanSpace.single b 1)) c =
      (pderiv a (pderiv b (pderiv c p))).eval (fun t => x t) := by
  let ev : (R3 →L[ℝ] R3) →L[ℝ] ℝ := (EuclideanSpace.proj c).comp
    (ContinuousLinearMap.apply ℝ R3 (EuclideanSpace.single b 1))
  have hSmooth : ContDiff ℝ ∞ (fun y => fderiv ℝ (gradient (smoothPolynomialData p).1) y) :=
    ((smoothPolynomialData p).2.gradient_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)
  have hFun : (fun y => ev (fderiv ℝ (gradient (smoothPolynomialData p).1) y)) =
      (fun y => (pderiv b (pderiv c p)).eval (polynomialCoordinateMap y)) := by
    funext y
    exact fderiv_polynomial_gradient_coordinate p y b c
  have hd := (ev.hasFDerivAt.comp x
    (hSmooth.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => ev (fderiv ℝ (gradient (smoothPolynomialData p).1) y)) x =
    ev.comp (fderiv ℝ (fun y => fderiv ℝ (gradient (smoothPolynomialData p).1) y) x) at hd
  rw [hFun] at hd
  have h := congrArg (fun A : R3 →L[ℝ] ℝ => A (EuclideanSpace.single a 1)) hd
  rw [← coordinateVector,fderiv_polynomialEval_coordinate] at h
  exact h.symm

lemma norm_sq_polynomial_thirdGradient_le (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    ‖TauCeti.iteratedGradientChain (smoothPolynomialData p).1 2 x‖^2 ≤
      3 * ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
        ((pderiv a (pderiv b (pderiv c p))).eval (fun t => x t))^2 := by
  let T : R3 →L[ℝ] R3 →L[ℝ] R3 :=
    fderiv ℝ (fun y => fderiv ℝ (gradient (smoothPolynomialData p).1) y) x
  change ‖T‖^2 ≤ _
  have hTop := norm_sq_clm_le_three_sum_coordinate_norms T
  calc
    ‖T‖^2 ≤ 3 * ∑ a : Fin 3, ‖T (EuclideanSpace.single a 1)‖^2 := hTop
    _ ≤ 3 * ∑ a : Fin 3, ∑ c : Fin 3, ∑ b : Fin 3,
        (((T (EuclideanSpace.single a 1)) (EuclideanSpace.single b 1)) c)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun a _ =>
        norm_sq_linearMap_le_coordinate_squares (T (EuclideanSpace.single a 1))
    _ = _ := by simp only [T,fderiv_polynomial_hessian_coordinate]

end OAI.AnisotropicCalderon.NativeHarmonicH3CoordinateBound
