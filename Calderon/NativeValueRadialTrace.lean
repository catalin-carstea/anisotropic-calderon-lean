import Calderon.NativePolynomialBallSobolev
import Calderon.SphereHarmonicBridge
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

/-- The genuine restricted values of a globally smooth datum on the actual sphere. -/
def smoothSphereValue (f : SmoothData) : C(UnitSphere, ℝ) :=
  ⟨fun x => f.1 x.val, f.2.continuous.comp continuous_subtype_val⟩

/-- A proposed standard value-trace witness. This structure asserts no existence theorem.
Its source-to-native adoption remains subject to three fresh independent audits. -/
structure UnitBallValueTrace where
  valueTraceL : BallH1 →L[ℝ] SphereL2
  valueTrace_smooth : ∀ f : SmoothData,
    valueTraceL (smoothSobolev f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f)

def sphereCoordinate (i : Fin 3) : C(UnitSphere, ℝ) :=
  ⟨fun x => x.val i, (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous.comp
    continuous_subtype_val⟩

theorem norm_sphereCoordinate_le (i : Fin 3) (x : UnitSphere) : ‖sphereCoordinate i x‖ ≤ 1 := by
  have hx : ‖x.val‖ = 1 := by
    simpa [UnitSphere, Metric.sphere, dist_eq_norm] using x.property
  exact (PiLp.norm_apply_le x.val i).trans_eq hx

theorem memLp_sphereCoordinate_mul (i : Fin 3) (u : SphereL2) :
    MemLp (fun x : UnitSphere => sphereCoordinate i x * u x) 2 sphereProbability := by
  apply (Lp.memLp u).of_le_mul (c := (1 : ℝ))
    ((sphereCoordinate i).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards with x
  change ‖sphereCoordinate i x * u x‖ ≤ 1 * ‖u x‖
  rw [norm_mul, one_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (norm_sphereCoordinate_le i x) (norm_nonneg (u x))

def sphereCoordinateMul (i : Fin 3) (u : SphereL2) : SphereL2 :=
  (memLp_sphereCoordinate_mul i u).toLp (fun x => sphereCoordinate i x * u x)

theorem sphereCoordinateMul_value_ae (i : Fin 3) (u : SphereL2) :
    sphereCoordinateMul i u =ᵐ[sphereProbability]
      (fun x : UnitSphere => sphereCoordinate i x * u x) :=
  (memLp_sphereCoordinate_mul i u).coeFn_toLp

def sphereCoordinateMulLinear (i : Fin 3) : SphereL2 →ₗ[ℝ] SphereL2 where
  toFun := sphereCoordinateMul i
  map_add' u v := by
    apply Lp.ext
    filter_upwards [sphereCoordinateMul_value_ae i (u + v),
      sphereCoordinateMul_value_ae i u, sphereCoordinateMul_value_ae i v,
      Lp.coeFn_add u v,
      Lp.coeFn_add (sphereCoordinateMul i u) (sphereCoordinateMul i v)]
      with x huv hu hv hadd hadd'
    simp only [huv, hadd', hu, hv, hadd, Pi.add_apply, mul_add]
  map_smul' c u := by
    change sphereCoordinateMul i (c • u) = c • sphereCoordinateMul i u
    apply Lp.ext
    filter_upwards [sphereCoordinateMul_value_ae i (c • u),
      sphereCoordinateMul_value_ae i u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (sphereCoordinateMul i u)] with x hcu hu hsmul hsmul'
    rw [hcu, hsmul']
    change sphereCoordinate i x * (c • u) x = c * (sphereCoordinateMul i u) x
    rw [hsmul, hu]
    change sphereCoordinate i x * (c * u x) = c * (sphereCoordinate i x * u x)
    ring

theorem norm_sphereCoordinateMul_le (i : Fin 3) (u : SphereL2) :
    ‖sphereCoordinateMul i u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sphereCoordinateMul_value_ae i u] with x hx
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (u x)) (norm_sphereCoordinate_le i x)

def sphereCoordinateMulL (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  (sphereCoordinateMulLinear i).mkContinuous 1
    (fun u => by
      change ‖sphereCoordinateMul i u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_sphereCoordinateMul_le i u)

theorem norm_sphereCoordinateMulL_le (i : Fin 3) : ‖sphereCoordinateMulL i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖sphereCoordinateMul i u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_sphereCoordinateMul_le i u

theorem sphereCoordinateMulL_toLp (i : Fin 3) (f : C(UnitSphere, ℝ)) :
    sphereCoordinateMulL i ((ContinuousMap.toLp 2 sphereProbability ℝ) f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (sphereCoordinate i * f) := by
  change sphereCoordinateMul i ((ContinuousMap.toLp 2 sphereProbability ℝ) f) =
    (ContinuousMap.toLp 2 sphereProbability ℝ) (sphereCoordinate i * f)
  apply Lp.ext
  filter_upwards [sphereCoordinateMul_value_ae i
      ((ContinuousMap.toLp 2 sphereProbability ℝ) f),
    ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ) f,
    ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ)
      (sphereCoordinate i * f)] with x hx hf hprod
  rw [hx, hf]
  change (sphereCoordinate i * f) x =
    ((ContinuousMap.toLp 2 sphereProbability ℝ) (sphereCoordinate i * f)) x
  exact hprod.symm

/-- Continuous ordinary outward radial trace in fixed unit-ball coordinates. -/
def outwardRadialTraceL (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) :
    BallSobolev 2 →L[ℝ] SphereL2 :=
  ∑ i : Fin 3, (sphereCoordinateMulL i).comp
    (τ0.valueTraceL.comp
      ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) 0).comp (unitBallCoordinateDerivativeL hcalc 1 i)))

theorem outwardRadialTraceL_apply (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (u : BallSobolev 2) :
    outwardRadialTraceL hcalc τ0 u = ∑ i : Fin 3,
      sphereCoordinateMulL i (τ0.valueTraceL
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u))) := by
  simp only [outwardRadialTraceL, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v : BallH1 => sphereCoordinateMulL i (τ0.valueTraceL v))
    (TauCeti.Wkp.firstOrderL_apply (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0 (unitBallCoordinateDerivativeL hcalc 1 i u))

theorem norm_outwardRadialTraceL_apply_le
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (u : BallSobolev 2) :
    ‖outwardRadialTraceL hcalc τ0 u‖ ≤
      ∑ i : Fin 3, ‖τ0.valueTraceL‖ * ‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖u‖ := by
  rw [outwardRadialTraceL_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc
    ‖sphereCoordinateMulL i (τ0.valueTraceL
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)))‖
        ≤ ‖τ0.valueTraceL
          (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u))‖ :=
      norm_sphereCoordinateMul_le i _
    _ ≤ ‖τ0.valueTraceL‖ *
        ‖TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i u)‖ :=
      τ0.valueTraceL.le_opNorm _
    _ ≤ ‖τ0.valueTraceL‖ * ‖unitBallCoordinateDerivativeL hcalc 1 i u‖ :=
      mul_le_mul_of_nonneg_left (norm_unitBall_firstOrder_le 0 _) τ0.valueTraceL.opNorm_nonneg
    _ ≤ ‖τ0.valueTraceL‖ * (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((unitBallCoordinateDerivativeL hcalc 1 i).le_opNorm u)
        τ0.valueTraceL.opNorm_nonneg
    _ = ‖τ0.valueTraceL‖ * ‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖u‖ := by ring

def smoothRadialSphere (f : SmoothData) : C(UnitSphere, ℝ) :=
  ⟨fun x => fderiv ℝ f.1 x.val x.val,
    ((f.2.continuous_fderiv (by simp)).comp continuous_subtype_val).clm_apply
      continuous_subtype_val⟩

theorem smoothRadialSphere_eq_sum (f : SmoothData) :
    smoothRadialSphere f = ∑ i : Fin 3,
      sphereCoordinate i * smoothSphereValue (smoothCoordinateDerivative f i) := by
  apply ContinuousMap.ext
  intro x
  change fderiv ℝ f.1 x.val x.val = (ContinuousMap.evalCLM ℝ x)
    (∑ i : Fin 3, sphereCoordinate i * smoothSphereValue (smoothCoordinateDerivative f i))
  rw [map_sum]
  change fderiv ℝ f.1 x.val x.val =
    ∑ i : Fin 3, x.val i * fderiv ℝ f.1 x.val (coordinateVector i)
  exact covector_coordinate_sum (fderiv ℝ f.1 x.val) x.val

theorem outwardRadialTraceL_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (f : SmoothData) :
    outwardRadialTraceL hcalc τ0 (smoothBallSobolev 2 f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothRadialSphere f) := by
  rw [outwardRadialTraceL_apply]
  calc
    _ = ∑ i : Fin 3, (ContinuousMap.toLp 2 sphereProbability ℝ)
        (sphereCoordinate i * smoothSphereValue (smoothCoordinateDerivative f i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [unitBallCoordinateDerivativeL_smoothBallSobolev hcalc 1 i f]
      rw [firstOrder_smoothBallSobolev 0 (smoothCoordinateDerivative f i)]
      rw [τ0.valueTrace_smooth (smoothCoordinateDerivative f i)]
      exact sphereCoordinateMulL_toLp i (smoothSphereValue (smoothCoordinateDerivative f i))
    _ = _ := by rw [← map_sum, ← smoothRadialSphere_eq_sum]

theorem outwardRadialTraceL_polynomialBallSobolev
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (p : MvPolynomial (Fin 3) ℝ) :
    outwardRadialTraceL hcalc τ0 (polynomialBallSobolev 2 p) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothRadialSphere (smoothPolynomialData p)) :=
  outwardRadialTraceL_smoothBallSobolev hcalc τ0 (smoothPolynomialData p)

theorem unitSphere_sum_sq (x : UnitSphere) : ∑ i : Fin 3, (x.val i) ^ 2 = 1 := by
  have hx : ‖x.val‖ = 1 := by
    simpa [UnitSphere, Metric.sphere, dist_eq_norm] using x.property
  simpa only [Real.norm_eq_abs, sq_abs, hx, one_pow] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.val).symm

theorem smoothRadialSphere_driftFirstVariation {k : ℕ} (hk : 1 ≤ k)
    (d : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    smoothRadialSphere (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k d p)) =
      (-(2 * (k : ℝ) + 1)⁻¹) • polynomialSphere (GreenRadialTrace.driftDerivative d p) := by
  ext x
  change fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y)
      (GreenRadialTrace.driftFirstVariation k d p)) x.val x.val =
    (-(2 * (k : ℝ) + 1)⁻¹) * eval (fun i => x.val i) (GreenRadialTrace.driftDerivative d p)
  rw [fderiv_polynomialEval_apply, ← GreenRadialTrace.fderiv_eval_apply,
    GreenRadialTrace.fderiv_driftFirstVariation_three_at_sphere hk d p
      (fun i => x.val i) (unitSphere_sum_sq x)]
  simp [GreenRadialTrace.driftDerivative, GreenRadialTrace.fderiv_eval_apply]

theorem outwardRadialTraceL_driftFirstVariation
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) {k : ℕ} (hk : 1 ≤ k)
    (d : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    outwardRadialTraceL hcalc τ0
      (polynomialBallSobolev 2 (GreenRadialTrace.driftFirstVariation k d p)) =
      (-(2 * (k : ℝ) + 1)⁻¹) • polynomialSphereL2 (GreenRadialTrace.driftDerivative d p) := by
  rw [outwardRadialTraceL_polynomialBallSobolev, smoothRadialSphere_driftFirstVariation hk]
  change (ContinuousMap.toLp 2 sphereProbability ℝ)
      ((-(2 * (k : ℝ) + 1)⁻¹) • polynomialSphere (GreenRadialTrace.driftDerivative d p)) =
    (-(2 * (k : ℝ) + 1)⁻¹) •
      (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (GreenRadialTrace.driftDerivative d p))
  exact map_smul _ _ _

/-- Parameter differentiation commutes with the fixed radial CLM by the chain rule. -/
theorem hasDerivAt_outwardRadialTraceL
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (f : ℝ → BallSobolev 2) (f' : BallSobolev 2) (r : ℝ) (hf : HasDerivAt f f' r) :
    HasDerivAt (fun t => outwardRadialTraceL hcalc τ0 (f t))
      (outwardRadialTraceL hcalc τ0 f') r := by
  simpa only [Function.comp_def] using
    (outwardRadialTraceL hcalc τ0).hasFDerivAt.comp_hasDerivAt r hf

end OAI.AnisotropicCalderon.DirichletFamily
