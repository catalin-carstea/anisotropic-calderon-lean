import Calderon.NativeValueRadialTrace

/-! Actual coordinate trace/first-variation geometry. All identities
come from the native smooth coordinate derivative and the literal explicit
zero-boundary polynomial; no boundary tangential trace premise is introduced. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError AngularPolynomial MetricVolume

def strongCoordinateTraceL (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (i : Fin 3) : BallSobolev 2 →L[ℝ] SphereL2 :=
  τ0.valueTraceL.comp ((TauCeti.Wkp.firstOrderL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0).comp
      (unitBallCoordinateDerivativeL hcalc 1 i))

theorem strongCoordinateTraceL_apply (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (i : Fin 3) (u : BallSobolev 2) :
    strongCoordinateTraceL hcalc τ0 i u =
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)) := by
  change τ0.valueTraceL ((TauCeti.Wkp.firstOrderL
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0)
      (unitBallCoordinateDerivativeL hcalc 1 i u)) = _
  exact congrArg τ0.valueTraceL (TauCeti.Wkp.firstOrderL_apply
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0
      (unitBallCoordinateDerivativeL hcalc 1 i u))

theorem strongCoordinateTraceL_smooth (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (i : Fin 3) (f : SmoothData) :
    strongCoordinateTraceL hcalc τ0 i (smoothBallSobolev 2 f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue (smoothCoordinateDerivative f i)) := by
  rw [strongCoordinateTraceL_apply,unitBallCoordinateDerivativeL_smoothBallSobolev,
    firstOrder_smoothBallSobolev,τ0.valueTrace_smooth]

theorem eval_pderiv_radialFirstVariation_at_sphere (m : ℕ)
    (q : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ)
    (hz : ∑ j : Fin 3, z j^2 = 1) (i : Fin 3) :
    MvPolynomial.eval z (MvPolynomial.pderiv i (AngularPolynomial.radialFirstVariation m q)) =
      z i * fderiv ℝ (fun x : Fin 3 → ℝ => MvPolynomial.eval x
        (AngularPolynomial.radialFirstVariation m q)) z z := by
  have hr : eval z (radiusSq : MvPolynomial (Fin 3) ℝ) = 1 := by simp [radiusSq,hz]
  rw [GreenRadialTrace.fderiv_radialFirstVariation_at_sphere m q z hz,radialFirstVariation]
  simp only [pderiv_mul,pderiv_C,zero_mul,zero_add,map_sub,pderiv_one,sub_zero,
    pderiv_radiusSq,map_mul,map_add,map_sub,map_ofNat,map_one,eval_C,eval_X,
    hr,sub_self,zero_mul,add_zero,div_eq_mul_inv]
  ring

theorem smoothSphereValue_coordinate_driftFirstVariation (k : ℕ)
    (d : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    smoothSphereValue (smoothCoordinateDerivative
      (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k d p)) i) =
      sphereCoordinate i * smoothRadialSphere
        (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k d p)) := by
  apply ContinuousMap.ext
  intro x
  change fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y)
      (GreenRadialTrace.driftFirstVariation k d p)) x.val (coordinateVector i) =
    x.val i * fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y)
      (GreenRadialTrace.driftFirstVariation k d p)) x.val x.val
  rw [fderiv_polynomialEval_coordinate,fderiv_polynomialEval_apply,
    ← GreenRadialTrace.fderiv_eval_apply]
  exact eval_pderiv_radialFirstVariation_at_sphere (k-1)
    (GreenRadialTrace.driftDerivative d p) (polynomialCoordinateMap x.val) (unitSphere_sum_sq x) i

theorem strongCoordinateTraceL_driftFirstVariation
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (k : ℕ) (d : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    strongCoordinateTraceL hcalc τ0 i
      (polynomialBallSobolev 2 (GreenRadialTrace.driftFirstVariation k d p)) =
      sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0
        (polynomialBallSobolev 2 (GreenRadialTrace.driftFirstVariation k d p))) := by
  change strongCoordinateTraceL hcalc τ0 i
    (smoothBallSobolev 2 (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k d p))) =
      sphereCoordinateMulL i (outwardRadialTraceL hcalc τ0
        (smoothBallSobolev 2 (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k d p))))
  rw [strongCoordinateTraceL_smooth,smoothSphereValue_coordinate_driftFirstVariation,
    outwardRadialTraceL_smoothBallSobolev,sphereCoordinateMulL_toLp]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
