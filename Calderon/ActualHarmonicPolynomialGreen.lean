import Calderon.ActualBallDivergenceFlux
import Calderon.NativeHarmonicBulkDerivativeMoments
import Calderon.NativeValueRadialTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set MvPolynomial
open scoped ContDiff Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.HarmonicPolynomialGreen
open RadialTestIntegration NativeHarmonicBulkDerivativeMoments NativePolynomialBulkMoments
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

/-! Expanded before source in EXPANSION-actual-harmonic-polynomial-Green-v001.json. -/

theorem contDiff_polynomial_energyGradient (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 1 (energyGradient (smoothPolynomialData p).1) := by
  have h := (smoothPolynomialData p).2.gradient_right (m := 1) (by simp)
  have he : energyGradient (smoothPolynomialData p).1 = gradient (smoothPolynomialData p).1 := by
    funext x
    exact energyGradient_eq_gradient _ x
  rw [he]
  exact h

theorem radialDivergence_euclidean_coordinates (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (x : R3) :
    radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) V x =
      ∑ i : Fin 3, fderiv ℝ (fun y : R3 => V y i) x (coordinateVector i) := by
  classical
  unfold radialDivergence
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have h := (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt.comp x
    (hV.differentiable (by norm_num) x).hasFDerivAt
  exact (congrArg (fun T : R3 →L[ℝ] ℝ => T (coordinateVector i)) h.fderiv).symm

theorem radialDivergence_smooth_polynomial_gradient_product
    (u : SmoothData) (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun y : R3 => u.1 y • energyGradient (smoothPolynomialData p).1 y) x =
        ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ +
          u.1 x * (AngularPolynomial.laplacian p).eval (polynomialCoordinateMap x) := by
  have hgrad := contDiff_polynomial_energyGradient p
  have hV : ContDiff ℝ 1 (fun y : R3 => u.1 y • energyGradient (smoothPolynomialData p).1 y) :=
    (u.2.of_le (by simp)).smul hgrad
  rw [radialDivergence_euclidean_coordinates _ hV]
  have hi (i : Fin 3) :
      fderiv ℝ (fun y : R3 => (u.1 y • energyGradient (smoothPolynomialData p).1 y) i)
        x (coordinateVector i) =
          u.1 x * (pderiv i (pderiv i p)).eval (polynomialCoordinateMap x) +
            fderiv ℝ u.1 x (coordinateVector i) * (pderiv i p).eval (polynomialCoordinateMap x) := by
    have he : (fun y : R3 => (u.1 y • energyGradient (smoothPolynomialData p).1 y) i) =
        (fun y : R3 => u.1 y * (pderiv i p).eval (polynomialCoordinateMap y)) := by
      funext y
      change u.1 y * energyGradient (smoothPolynomialData p).1 y i = _
      rw [polynomial_energyGradient_coordinate]
      rfl
    rw [he, fderiv_fun_mul (u.2.differentiable (by simp) x)
      ((contDiff_polynomialEval (pderiv i p)).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_polynomialEval_coordinate]
    simp only [polynomialCoordinateMap_apply]
    ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hinner : ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ =
      ∑ i : Fin 3, fderiv ℝ u.1 x (coordinateVector i) *
        (pderiv i p).eval (polynomialCoordinateMap x) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply,polynomial_energyGradient_coordinate,energyGradient_apply]
    rfl
  have hlap : (AngularPolynomial.laplacian p).eval (polynomialCoordinateMap x) =
      ∑ i : Fin 3, (pderiv i (pderiv i p)).eval (polynomialCoordinateMap x) := by
    rw [AngularPolynomial.laplacian, map_sum]
  rw [← hinner, ← hlap]
  ring

theorem inner_polynomial_energyGradient_radial (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (x : R3) :
    ⟪x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ =
      (k : ℝ) * p.eval (polynomialCoordinateMap x) := by
  rw [energyGradient_eq_gradient, inner_gradient_right]
  simp only [RCLike.conj_to_real]
  change fderiv ℝ (fun y : R3 => p.eval (polynomialCoordinateMap y)) x x = _
  rw [fderiv_polynomialEval_apply]
  have h := congrArg (eval (polynomialCoordinateMap x)) hp.sum_X_mul_pderiv
  simpa only [map_sum,map_mul,eval_X,map_natCast,map_nsmul,nsmul_eq_mul,
    polynomialCoordinateMap_apply] using h

theorem integral_unitBall_gradient_harmonicPolynomial (u : SmoothData) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∫ x in ball (0 : R3) 1,
      ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ) =
        (k : ℝ) * ∫ «ω» : UnitSphere, u.1 «ω».val * p.eval (polynomialCoordinateMap «ω».val)
          ∂surfaceMeasure := by
  have hV : ContDiff ℝ 1 (fun y : R3 => u.1 y • energyGradient (smoothPolynomialData p).1 y) :=
    (u.2.of_le (by simp)).smul (contDiff_polynomial_energyGradient p)
  have h := integral_unitBall_radialDivergence_eq_surfaceFlux
    (EuclideanSpace.basisFun (Fin 3) ℝ) _ hV
  have hdiv : radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun y : R3 => u.1 y • energyGradient (smoothPolynomialData p).1 y) =
        (fun x : R3 => ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ) := by
    funext x
    rw [radialDivergence_smooth_polynomial_gradient_product, hp.2, map_zero, mul_zero, add_zero]
  rw [hdiv] at h
  calc
    _ = ∫ «ω» : UnitSphere, ⟪«ω».val,u.1 «ω».val • energyGradient (smoothPolynomialData p).1 «ω».val⟫_ℝ
        ∂surfaceMeasure := h
    _ = ∫ «ω» : UnitSphere, (k : ℝ) * (u.1 «ω».val * p.eval (polynomialCoordinateMap «ω».val))
        ∂surfaceMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ (fun «ω» => by
        dsimp only
        rw [real_inner_smul_right, inner_polynomial_energyGradient_radial k p hp.1]
        ring)
    _ = _ := integral_const_mul _ _

theorem integral_unitBall_gradient_harmonicPolynomial_trace
    (τ0 : UnitBallValueTrace) (u : SmoothData) (k : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    (∫ x in ball (0 : R3) 1,
      ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ) =
        sphereSurfaceMass * (k : ℝ) *
          ⟪τ0.valueTraceL (smoothSobolev u),polynomialSphereL2 p⟫_ℝ := by
  have hi : ⟪τ0.valueTraceL (smoothSobolev u),polynomialSphereL2 p⟫_ℝ =
      ∫ «ω» : UnitSphere, u.1 «ω».val * p.eval (polynomialCoordinateMap «ω».val)
        ∂sphereProbability := by
    rw [τ0.valueTrace_smooth]
    change ⟪(ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue u),
      (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere p)⟫_ℝ = _
    rw [ContinuousMap.inner_toLp sphereProbability (smoothSphereValue u) (polynomialSphere p)]
    apply integral_congr_ae
    exact ae_of_all sphereProbability (fun «ω» => by
      simp only [starRingEnd_apply,star_trivial]
      change p.eval (fun i => «ω».val i) * u.1 «ω».val =
        u.1 «ω».val * p.eval (polynomialCoordinateMap «ω».val)
      simp only [polynomialCoordinateMap_apply]
      ring)
  rw [integral_unitBall_gradient_harmonicPolynomial u k p hp,
    integral_surface_eq_mass_probability, ← hi]
  ring

end OAI.AnisotropicCalderon.HarmonicPolynomialGreen

#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.contDiff_polynomial_energyGradient
#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.radialDivergence_euclidean_coordinates
#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.radialDivergence_smooth_polynomial_gradient_product
#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.inner_polynomial_energyGradient_radial
#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.integral_unitBall_gradient_harmonicPolynomial
#print axioms OAI.AnisotropicCalderon.HarmonicPolynomialGreen.integral_unitBall_gradient_harmonicPolynomial_trace
