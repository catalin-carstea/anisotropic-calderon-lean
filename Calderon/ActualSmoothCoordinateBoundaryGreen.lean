import Calderon.ActualHarmonicPolynomialGreen

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ContDiff InnerProductSpace Gradient Classical
namespace OAI.AnisotropicCalderon.SmoothCoordinateBoundaryGreen
open HarmonicPolynomialGreen RadialTestIntegration NativePolynomialBulkMoments
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

lemma radialDivergence_scalar_coordinate (q : R3 → ℝ) (hq : ContDiff ℝ 1 q)
    (i : Fin 3) (x : R3) :
    radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun y : R3 => q y • coordinateVector i) x = fderiv ℝ q x (coordinateVector i) := by
  have hV : ContDiff ℝ 1 (fun y : R3 => q y • coordinateVector i) := hq.smul contDiff_const
  rw [radialDivergence_euclidean_coordinates _ hV]
  have hj (j : Fin 3) :
      fderiv ℝ (fun y : R3 => (q y • coordinateVector i) j) x (coordinateVector j) =
        coordinateVector i j * fderiv ℝ q x (coordinateVector j) := by
    have he : (fun y : R3 => (q y • coordinateVector i) j) =
        (fun y : R3 => q y * coordinateVector i j) := by
      funext y
      rfl
    rw [he,fderiv_fun_mul (hq.differentiable (by norm_num) x) (differentiableAt_const (coordinateVector i j))]
    simp only [fderiv_const_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,ContinuousLinearMap.zero_apply,mul_zero,zero_add]
  simp_rw [hj]
  rw [Finset.sum_eq_single i]
  · simp only [coordinateVector,EuclideanSpace.single_apply,ite_true,one_mul]
  · intro j hj hji
    simp only [coordinateVector,EuclideanSpace.single_apply,hji,ite_false,zero_mul]
  · simp

lemma integral_coordinate_smooth_product_surface (F v : SmoothData) (i : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      fderiv ℝ F.1 x (coordinateVector i)*v.1 x + F.1 x*fderiv ℝ v.1 x (coordinateVector i)) =
        ∫ «ω» : UnitSphere, «ω».val i * F.1 «ω».val * v.1 «ω».val ∂surfaceMeasure := by
  have hq : ContDiff ℝ 1 (fun x : R3 => F.1 x * v.1 x) :=
    (F.2.mul v.2).of_le (by simp)
  have hV : ContDiff ℝ 1 (fun x : R3 => (F.1 x * v.1 x) • coordinateVector i) :=
    hq.smul contDiff_const
  have hd : radialDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun x : R3 => (F.1 x * v.1 x) • coordinateVector i) =
        (fun x : R3 => fderiv ℝ F.1 x (coordinateVector i)*v.1 x +
          F.1 x*fderiv ℝ v.1 x (coordinateVector i)) := by
    funext x
    rw [radialDivergence_scalar_coordinate _ hq,
      fderiv_fun_mul (F.2.differentiable (by simp) x) (v.2.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have h := integral_unitBall_radialDivergence_eq_surfaceFlux
    (EuclideanSpace.basisFun (Fin 3) ℝ) _ hV
  rw [hd] at h
  calc
    _ = ∫ «ω» : UnitSphere, ⟪«ω».val,(F.1 «ω».val*v.1 «ω».val) • coordinateVector i⟫_ℝ
        ∂surfaceMeasure := h
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all surfaceMeasure (fun «ω» => by
        dsimp only
        rw [real_inner_smul_right]
        simp only [coordinateVector,EuclideanSpace.inner_single_right,conj_trivial,mul_one]
        ring)

lemma integral_coordinate_smooth_product_probability (F v : SmoothData) (i : Fin 3) :
    (∫ x in Metric.ball (0 : R3) 1,
      fderiv ℝ F.1 x (coordinateVector i)*v.1 x + F.1 x*fderiv ℝ v.1 x (coordinateVector i)) =
        sphereSurfaceMass * ∫ «ω» : UnitSphere,
          «ω».val i * F.1 «ω».val * v.1 «ω».val ∂sphereProbability := by
  rw [integral_coordinate_smooth_product_surface,integral_surface_eq_mass_probability]

end OAI.AnisotropicCalderon.SmoothCoordinateBoundaryGreen

#print axioms OAI.AnisotropicCalderon.SmoothCoordinateBoundaryGreen.radialDivergence_scalar_coordinate
#print axioms OAI.AnisotropicCalderon.SmoothCoordinateBoundaryGreen.integral_coordinate_smooth_product_surface
#print axioms OAI.AnisotropicCalderon.SmoothCoordinateBoundaryGreen.integral_coordinate_smooth_product_probability
