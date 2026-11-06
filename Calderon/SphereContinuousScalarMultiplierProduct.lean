import Calderon.SphereContinuousScalarMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

theorem sphereContinuousScalarMulL_mul_apply
    (c d : C(UnitSphere, ℝ)) (u : SphereL2) :
    sphereContinuousScalarMulL c (sphereContinuousScalarMulL d u) =
      sphereContinuousScalarMulL (c*d) u := by
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae c (sphereContinuousScalarMulL d u),
    sphereContinuousScalarMul_value_ae d u,
    sphereContinuousScalarMul_value_ae (c*d) u] with x hc hd hcd
  change sphereContinuousScalarMul c (sphereContinuousScalarMulL d u) x =
    sphereContinuousScalarMul (c*d) u x
  rw [hc,hcd]
  change c x * (sphereContinuousScalarMul d u) x = (c x*d x)*u x
  rw [hd,mul_assoc]

theorem sphereContinuousScalarMulL_comp_eq_id_of_mul_eq_one
    (c d : C(UnitSphere, ℝ)) (hcd : ∀ x, c x*d x = 1) :
    (sphereContinuousScalarMulL c).comp (sphereContinuousScalarMulL d) =
      ContinuousLinearMap.id ℝ SphereL2 := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereContinuousScalarMulL c (sphereContinuousScalarMulL d u) = u
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae c (sphereContinuousScalarMulL d u),
    sphereContinuousScalarMul_value_ae d u] with x hc hd
  change sphereContinuousScalarMul c (sphereContinuousScalarMulL d u) x = u x
  rw [hc]
  change c x * (sphereContinuousScalarMul d u) x = u x
  rw [hd,← mul_assoc,hcd x,one_mul]

end OAI.AnisotropicCalderon.DirichletFamily
