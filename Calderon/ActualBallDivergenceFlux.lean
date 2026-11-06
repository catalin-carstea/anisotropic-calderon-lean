import Calderon.ActualSphereFluxContinuity
import Calderon.IntervalDistributionPrimitive

set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.RadialTestIntegration
open SphereHarmonic IntervalDistributionPrimitive

/-! Expanded before source in EXPANSION-actual-ball-divergence-flux-v001.json. -/

theorem integral_ball_zero_eq_radial_interval (f : R3 → ℝ) (R : ℝ) (hR : 0 < R)
    (hf : IntegrableOn f (ball (0 : R3) R) (volume : Measure R3)) :
    (∫ x in ball (0 : R3) R, f x) = ∫ r in (0 : ℝ)..R, r^2 *
      ∫ «ω» : UnitSphere, f (r • «ω».val) ∂surfaceMeasure := by
  have hint : Integrable ((ball (0 : R3) R).indicator f) (volume : Measure R3) :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_eq_integral_Ioi_surface _ hint]
  have hinner : ∀ r ∈ Ioi (0 : ℝ), r^2 *
      (∫ «ω» : UnitSphere, (ball (0 : R3) R).indicator f (r • «ω».val) ∂surfaceMeasure) =
        (Iio R).indicator (fun r : ℝ => r^2 *
          ∫ «ω» : UnitSphere, f (r • «ω».val) ∂surfaceMeasure) r := by
    intro r hr
    have hmem («ω» : UnitSphere) : r • «ω».val ∈ ball (0 : R3) R ↔ r < R := by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere «ω», mul_one,
        Real.norm_of_nonneg hr.le]
    by_cases hrR : r < R
    · rw [indicator_of_mem (mem_Iio.mpr hrR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hrR)]
    · rw [indicator_of_notMem (by simpa using hrR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hrR)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]

theorem sphereFlux_eq_intervalPrimitive
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (R : ℝ) (hR : 0 < R) :
    EqOn (sphereFlux V) (intervalPrimitive (sphereDivergenceProfile b V))
      (Icc (0 : ℝ) R) := by
  apply eq_intervalPrimitive_of_integral_test (sphereFlux V) (sphereDivergenceProfile b V) R hR
    (continuousOn_sphereFlux V hV.continuous R)
    (continuousOn_sphereDivergenceProfile b V hV R) (sphereFlux_zero V)
  intro ψ hψ hψs
  exact integral_test_sphereDivergenceProfile b V hV R hR ψ hψ hψs

theorem integral_ball_radialDivergence_eq_sphereFlux
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V)
    (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : R3) R, radialDivergence b V x) =
      R^2 * ∫ «ω» : UnitSphere, ⟪«ω».val,V (R • «ω».val)⟫_ℝ ∂surfaceMeasure := by
  have hc : Continuous (radialDivergence b V) := by
    unfold radialDivergence
    apply continuous_finset_sum
    intro i hi
    exact (innerSL ℝ (b i)).continuous.comp
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hint : IntegrableOn (radialDivergence b V) (ball (0 : R3) R) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : R3) R)).mono_set
      ball_subset_closedBall
  rw [integral_ball_zero_eq_radial_interval _ R hR hint]
  change intervalPrimitive (sphereDivergenceProfile b V) R = sphereFlux V R
  exact ((sphereFlux_eq_intervalPrimitive b V hV R hR) ⟨hR.le,le_rfl⟩).symm

theorem integral_unitBall_radialDivergence_eq_surfaceFlux
    (b : OrthonormalBasis (Fin 3) ℝ R3) (V : R3 → R3) (hV : ContDiff ℝ 1 V) :
    (∫ x in ball (0 : R3) 1, radialDivergence b V x) =
      ∫ «ω» : UnitSphere, ⟪«ω».val,V «ω».val⟫_ℝ ∂surfaceMeasure := by
  simpa only [one_pow, one_mul, one_smul] using
    integral_ball_radialDivergence_eq_sphereFlux b V hV 1 (by norm_num)

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_ball_zero_eq_radial_interval
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.sphereFlux_eq_intervalPrimitive
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_ball_radialDivergence_eq_sphereFlux
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.integral_unitBall_radialDivergence_eq_surfaceFlux
