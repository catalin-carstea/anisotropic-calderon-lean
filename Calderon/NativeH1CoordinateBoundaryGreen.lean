import Calderon.ActualSmoothCoordinateBoundaryGreen
import Calderon.CoordinateWeakIntegration
import Calderon.NativeGlobalSmoothH1Density
import Calderon.NativeValueRadialTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Gradient Classical
namespace OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen
open SmoothCoordinateBoundaryGreen NativePolynomialBulkMoments
  SphereHarmonic DirichletFamily EnergyBridge MetricVolume

/-! Density is the imported actual smooth density theorem on the native H1 graph. -/

lemma unitBallCoordinateGradientL_smoothSobolev_ae (f : SmoothData) (i : Fin 3) :
    unitBallCoordinateGradientL i (smoothSobolev f) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => fderiv ℝ f.1 x (coordinateVector i)) := by
  filter_upwards [unitBallCoordinateGradientL_ae i (smoothSobolev f),
    gradient_smoothSobolev_ae f] with x hc hg
  rw [hc,hg,← energyGradient_eq_gradient]
  rfl

lemma coordinate_bulk_inner_smooth_product (F v : SmoothData) (i : Fin 3) :
    ⟪unitBallCoordinateGradientL i (smoothSobolev F),TauCeti.W1p.value (smoothSobolev v)⟫_ℝ +
      ⟪TauCeti.W1p.value (smoothSobolev F),unitBallCoordinateGradientL i (smoothSobolev v)⟫_ℝ =
        ∫ x in Metric.ball (0 : R3) 1,
          fderiv ℝ F.1 x (coordinateVector i)*v.1 x + F.1 x*fderiv ℝ v.1 x (coordinateVector i) := by
  rw [L2.inner_def,L2.inner_def]
  rw [← integral_add
    (L2.integrable_inner (𝕜 := ℝ) (unitBallCoordinateGradientL i (smoothSobolev F))
      (TauCeti.W1p.value (smoothSobolev v)))
    (L2.integrable_inner (𝕜 := ℝ) (TauCeti.W1p.value (smoothSobolev F))
      (unitBallCoordinateGradientL i (smoothSobolev v)))]
  apply integral_congr_ae
  filter_upwards [unitBallCoordinateGradientL_smoothSobolev_ae F i,
    unitBallCoordinateGradientL_smoothSobolev_ae v i,
    value_smoothSobolev_ae F,value_smoothSobolev_ae v] with x hF hv hVF hVv
  rw [hF,hv,hVF,hVv,Real.inner_apply,Real.inner_apply]

lemma coordinate_boundary_inner_smooth_product
    (τ0 : UnitBallValueTrace) (F v : SmoothData) (i : Fin 3) :
    ⟪sphereCoordinateMulL i (τ0.valueTraceL (smoothSobolev F)),
      τ0.valueTraceL (smoothSobolev v)⟫_ℝ =
        ∫ «ω» : UnitSphere, «ω».val i * F.1 «ω».val * v.1 «ω».val ∂sphereProbability := by
  rw [τ0.valueTrace_smooth,τ0.valueTrace_smooth,sphereCoordinateMulL_toLp]
  rw [ContinuousMap.inner_toLp sphereProbability
    (sphereCoordinate i * smoothSphereValue F) (smoothSphereValue v)]
  apply integral_congr_ae
  exact ae_of_all sphereProbability (fun «ω» => by
    simp only [starRingEnd_apply,star_trivial]
    change v.1 «ω».val * («ω».val i * F.1 «ω».val) =
      «ω».val i * F.1 «ω».val * v.1 «ω».val
    ring)

lemma unitBall_coordinate_boundary_inner_smooth
    (τ0 : UnitBallValueTrace) (F v : SmoothData) (i : Fin 3) :
    ⟪unitBallCoordinateGradientL i (smoothSobolev F),TauCeti.W1p.value (smoothSobolev v)⟫_ℝ +
      ⟪TauCeti.W1p.value (smoothSobolev F),unitBallCoordinateGradientL i (smoothSobolev v)⟫_ℝ =
        sphereSurfaceMass * ⟪sphereCoordinateMulL i (τ0.valueTraceL (smoothSobolev F)),
          τ0.valueTraceL (smoothSobolev v)⟫_ℝ := by
  rw [coordinate_bulk_inner_smooth_product,coordinate_boundary_inner_smooth_product,
    integral_coordinate_smooth_product_probability]

lemma unitBall_coordinate_boundary_inner
    (τ0 : UnitBallValueTrace) (F v : BallH1) (i : Fin 3) :
    ⟪unitBallCoordinateGradientL i F,TauCeti.W1p.value v⟫_ℝ +
      ⟪TauCeti.W1p.value F,unitBallCoordinateGradientL i v⟫_ℝ =
        sphereSurfaceMass * ⟪sphereCoordinateMulL i (τ0.valueTraceL F),τ0.valueTraceL v⟫_ℝ := by
  apply denseRange_smoothSobolev.induction_on₂
    (p := fun F v : BallH1 =>
      ⟪unitBallCoordinateGradientL i F,TauCeti.W1p.value v⟫_ℝ +
        ⟪TauCeti.W1p.value F,unitBallCoordinateGradientL i v⟫_ℝ =
          sphereSurfaceMass * ⟪sphereCoordinateMulL i (τ0.valueTraceL F),τ0.valueTraceL v⟫_ℝ)
  · apply isClosed_eq
    · exact (((unitBallCoordinateGradientL i).continuous.comp continuous_fst).inner
        (TauCeti.W1p.valueL.continuous.comp continuous_snd)).add
          ((TauCeti.W1p.valueL.continuous.comp continuous_fst).inner
            ((unitBallCoordinateGradientL i).continuous.comp continuous_snd))
    · exact continuous_const.mul
        (((sphereCoordinateMulL i).continuous.comp
          (τ0.valueTraceL.continuous.comp continuous_fst)).inner
            (τ0.valueTraceL.continuous.comp continuous_snd))
  · intro F v
    exact unitBall_coordinate_boundary_inner_smooth τ0 F v i

end OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen

#print axioms OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen.unitBallCoordinateGradientL_smoothSobolev_ae
#print axioms OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen.coordinate_bulk_inner_smooth_product
#print axioms OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen.coordinate_boundary_inner_smooth_product
#print axioms OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen.unitBall_coordinate_boundary_inner_smooth
#print axioms OAI.AnisotropicCalderon.NativeH1CoordinateBoundaryGreen.unitBall_coordinate_boundary_inner
