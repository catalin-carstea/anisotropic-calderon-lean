import Calderon.NativeWeakMixedCoordinateDerivative
import Calderon.NativeH1CoordinateBoundaryGreen
import Calderon.NativeCoordinateTraceVariation
import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic DriftBootstrap
  NativeH1CoordinateBoundaryGreen NativeSmoothSharpTraceCompletion NativePolynomialBulkMoments
  SmoothSphereRotation SmoothAngularCasimir

/-! Expansion: EXPANSION-native-H2-tangential-trace-v001.md, obligations B-C. -/

theorem inner_sphereCoordinateMulL_left (i : Fin 3) (u v : SphereL2) :
    ⟪sphereCoordinateMulL i u,v⟫_ℝ = ⟪u,sphereCoordinateMulL i v⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereCoordinateMul_value_ae i u,sphereCoordinateMul_value_ae i v]
    with x hu hv
  change ⟪sphereCoordinateMul i u x,v x⟫_ℝ = ⟪u x,sphereCoordinateMul i v x⟫_ℝ
  rw [hu,hv]
  change ⟪sphereCoordinate i x • u x,v x⟫_ℝ = ⟪u x,sphereCoordinate i x • v x⟫_ℝ
  rw [real_inner_smul_left,real_inner_smul_right]

theorem unitBallCoordinateGradient_smoothSobolev_eq_value
    (f : SmoothData) (i : Fin 3) :
    unitBallCoordinateGradientL i (smoothSobolev f) =
      TauCeti.W1p.value (smoothSobolev (smoothCoordinateDerivative f i)) := by
  apply Lp.ext
  exact (unitBallCoordinateGradientL_smoothSobolev_ae f i).trans
    (value_smoothSobolev_ae (smoothCoordinateDerivative f i)).symm

theorem boundary_rotation_inner_of_green
    {U H S : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    (D : Fin 3 → U → H) (value : U → H) (trace : U → S)
    (M : Fin 3 → S → S) (mass : ℝ) (hmass : mass ≠ 0)
    (hGreen : ∀ u v k, ⟪D k u,value v⟫_ℝ + ⟪value u,D k v⟫_ℝ =
      mass * ⟪M k (trace u),trace v⟫_ℝ)
    (hSelf : ∀ k x y, ⟪M k x,y⟫_ℝ = ⟪x,M k y⟫_ℝ)
    (u di dj f fi fj : U) (i j : Fin 3)
    (hdi : value di = D i u) (hdj : value dj = D j u)
    (hMixed : D j di = D i dj)
    (hfi : value fi = D i f) (hfj : value fj = D j f)
    (hSmoothMixed : D i fj = D j fi) :
    ⟪M j (trace di)-M i (trace dj),trace f⟫_ℝ =
      -⟪trace u,M j (trace fi)-M i (trace fj)⟫_ℝ := by
  have h1 := hGreen di f j
  have h2 := hGreen dj f i
  have h3 := hGreen u fj i
  have h4 := hGreen u fi j
  rw [hdi,hMixed] at h1
  rw [hdj] at h2
  rw [hfj,hSmoothMixed,hSelf] at h3
  rw [hfi,hSelf] at h4
  apply (mul_left_cancel₀ hmass)
  rw [inner_sub_left,inner_sub_right,mul_neg,mul_sub,mul_sub]
  linarith

theorem nativeH2_boundary_coordinate_rotation_inner
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (U : BallSobolev 2) (f : SmoothData) (i j : Fin 3) :
    ⟪sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
        sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U),
      τ0.valueTraceL (smoothSobolev f)⟫_ℝ =
    -⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U),
      sphereCoordinateMulL j (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i))) -
        sphereCoordinateMulL i (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f j)))⟫_ℝ := by
  let u := TauCeti.Wkp.firstOrder 1 U
  let di := TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)
  let dj := TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j U)
  have hdi : TauCeti.W1p.value di = unitBallCoordinateGradientL i u := by
    rw [TauCeti.Wkp.value_firstOrder,unitBallCoordinateDerivative_eq_coordinateGradient]
  have hdj : TauCeti.W1p.value dj = unitBallCoordinateGradientL j u := by
    rw [TauCeti.Wkp.value_firstOrder,unitBallCoordinateDerivative_eq_coordinateGradient]
  have hMixed : unitBallCoordinateGradientL j di = unitBallCoordinateGradientL i dj :=
    unitBallCoordinateGradient_mixed_commute hcalc U i j
  have hSmoothMixed :
      unitBallCoordinateGradientL i (smoothSobolev (smoothCoordinateDerivative f j)) =
        unitBallCoordinateGradientL j (smoothSobolev (smoothCoordinateDerivative f i)) := by
    rw [unitBallCoordinateGradient_smoothSobolev_eq_value,
      unitBallCoordinateGradient_smoothSobolev_eq_value,smoothCoordinateDerivative_commute f i j]
  have hcore := boundary_rotation_inner_of_green
    (fun (k : Fin 3) (v : BallH1) => unitBallCoordinateGradientL k v)
    (fun v : BallH1 => TauCeti.W1p.value v)
    (fun v : BallH1 => τ0.valueTraceL v)
    (fun k v => sphereCoordinateMulL k v) sphereSurfaceMass sphereSurfaceMass_pos.ne'
    (unitBall_coordinate_boundary_inner τ0) inner_sphereCoordinateMulL_left
    u di dj (smoothSobolev f)
    (smoothSobolev (smoothCoordinateDerivative f i))
    (smoothSobolev (smoothCoordinateDerivative f j)) i j hdi hdj hMixed
    (unitBallCoordinateGradient_smoothSobolev_eq_value f i).symm
    (unitBallCoordinateGradient_smoothSobolev_eq_value f j).symm hSmoothMixed
  have hti : strongCoordinateTraceL hcalc τ0 i U = τ0.valueTraceL di :=
    strongCoordinateTraceL_apply hcalc τ0 i U
  have htj : strongCoordinateTraceL hcalc τ0 j U = τ0.valueTraceL dj :=
    strongCoordinateTraceL_apply hcalc τ0 j U
  have hleft := congrArg₂ (fun bi bj : SphereL2 =>
    ⟪sphereCoordinateMulL j bi-sphereCoordinateMulL i bj,
      τ0.valueTraceL (smoothSobolev f)⟫_ℝ) hti htj
  exact hleft.trans hcore

theorem smoothSphereLift_rotation_eq_coordinate_trace
    (τ0 : UnitBallValueTrace) (f : SmoothData) (i j : Fin 3) :
    smoothSphereLift (sphereRotationDerivative j i f.1)
      (contDiff_sphereRotationDerivative j i f.1 f.2) =
      sphereCoordinateMulL j (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f i))) -
        sphereCoordinateMulL i (τ0.valueTraceL (smoothSobolev (smoothCoordinateDerivative f j))) := by
  rw [τ0.valueTrace_smooth,τ0.valueTrace_smooth,
    sphereCoordinateMulL_toLp,sphereCoordinateMulL_toLp,← map_sub]
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1
  ext x
  change fderiv ℝ f.1 x.val (x.val j • coordinateVector i-x.val i • coordinateVector j) =
    x.val j * fderiv ℝ f.1 x.val (coordinateVector i) -
      x.val i * fderiv ℝ f.1 x.val (coordinateVector j)
  rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]

theorem nativeH2_boundary_rotation_inner_smooth
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (U : BallSobolev 2) (f : SmoothData) (i j : Fin 3) :
    ⟪sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 i U) -
        sphereCoordinateMulL i (strongCoordinateTraceL hcalc τ0 j U),
      τ0.valueTraceL (smoothSobolev f)⟫_ℝ =
    -⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U),
      smoothSphereLift (sphereRotationDerivative j i f.1)
        (contDiff_sphereRotationDerivative j i f.1 f.2)⟫_ℝ := by
  rw [smoothSphereLift_rotation_eq_coordinate_trace]
  exact nativeH2_boundary_coordinate_rotation_inner hcalc τ0 U f i j

end OAI.AnisotropicCalderon.DirichletFamily
