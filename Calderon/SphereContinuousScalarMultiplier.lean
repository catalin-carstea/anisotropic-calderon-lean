import Calderon.NativeValueRadialTrace

/-! Genuine multiplication by a continuous scalar on the actual probability sphere. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

theorem memLp_sphereContinuousScalar_mul (c : C(UnitSphere, ℝ)) (u : SphereL2) :
    MemLp (fun x : UnitSphere => c x * u x) 2 sphereProbability := by
  apply (Lp.memLp u).of_le_mul (c := ‖c‖)
    ((c).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  filter_upwards with x
  change ‖c x * u x‖ ≤ ‖c‖ * ‖u x‖
  rw [norm_mul]
  exact
    mul_le_mul_of_nonneg_right (c.norm_coe_le_norm x) (norm_nonneg (u x))

def sphereContinuousScalarMul (c : C(UnitSphere, ℝ)) (u : SphereL2) : SphereL2 :=
  (memLp_sphereContinuousScalar_mul c u).toLp (fun x => c x * u x)

theorem sphereContinuousScalarMul_value_ae (c : C(UnitSphere, ℝ)) (u : SphereL2) :
    sphereContinuousScalarMul c u =ᵐ[sphereProbability]
      (fun x : UnitSphere => c x * u x) :=
  (memLp_sphereContinuousScalar_mul c u).coeFn_toLp

def sphereContinuousScalarMulLinear (c : C(UnitSphere, ℝ)) : SphereL2 →ₗ[ℝ] SphereL2 where
  toFun := sphereContinuousScalarMul c
  map_add' u v := by
    apply Lp.ext
    filter_upwards [sphereContinuousScalarMul_value_ae c (u + v),
      sphereContinuousScalarMul_value_ae c u, sphereContinuousScalarMul_value_ae c v,
      Lp.coeFn_add u v,
      Lp.coeFn_add (sphereContinuousScalarMul c u) (sphereContinuousScalarMul c v)]
      with x huv hu hv hadd hadd'
    simp only [huv, hadd', hu, hv, hadd, Pi.add_apply, mul_add]
  map_smul' t u := by
    change sphereContinuousScalarMul c (t • u) = t • sphereContinuousScalarMul c u
    apply Lp.ext
    filter_upwards [sphereContinuousScalarMul_value_ae c (t • u),
      sphereContinuousScalarMul_value_ae c u, Lp.coeFn_smul t u,
      Lp.coeFn_smul t (sphereContinuousScalarMul c u)] with x hcu hu hsmul hsmul'
    rw [hcu, hsmul']
    change c x * (t • u) x = t * (sphereContinuousScalarMul c u) x
    rw [hsmul, hu]
    change c x * (t * u x) = t * (c x * u x)
    ring

theorem norm_sphereContinuousScalarMul_le (c : C(UnitSphere, ℝ)) (u : SphereL2) :
    ‖sphereContinuousScalarMul c u‖ ≤ ‖c‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [sphereContinuousScalarMul_value_ae c u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (c.norm_coe_le_norm x) (norm_nonneg (u x))

def sphereContinuousScalarMulL (c : C(UnitSphere, ℝ)) : SphereL2 →L[ℝ] SphereL2 :=
  (sphereContinuousScalarMulLinear c).mkContinuous ‖c‖
    (fun u => by
      change ‖sphereContinuousScalarMul c u‖ ≤ ‖c‖ * ‖u‖
      exact norm_sphereContinuousScalarMul_le c u)

theorem norm_sphereContinuousScalarMulL_le (c : C(UnitSphere, ℝ)) : ‖sphereContinuousScalarMulL c‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro u
  change ‖sphereContinuousScalarMul c u‖ ≤ ‖c‖ * ‖u‖
  exact norm_sphereContinuousScalarMul_le c u

theorem sphereContinuousScalarMulL_toLp (c : C(UnitSphere, ℝ)) (f : C(UnitSphere, ℝ)) :
    sphereContinuousScalarMulL c ((ContinuousMap.toLp 2 sphereProbability ℝ) f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (c * f) := by
  change sphereContinuousScalarMul c ((ContinuousMap.toLp 2 sphereProbability ℝ) f) =
    (ContinuousMap.toLp 2 sphereProbability ℝ) (c * f)
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae c
      ((ContinuousMap.toLp 2 sphereProbability ℝ) f),
    ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ) f,
    ContinuousMap.coeFn_toLp (p := 2) (μ := sphereProbability) (𝕜 := ℝ)
      (c * f)] with x hx hf hprod
  rw [hx, hf]
  change (c * f) x =
    ((ContinuousMap.toLp 2 sphereProbability ℝ) (c * f)) x
  exact hprod.symm


end OAI.AnisotropicCalderon.DirichletFamily
