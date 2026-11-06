import Calderon.SphereContinuousScalarMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

def sphereContinuousScalarMultiplierL : C(UnitSphere,ℝ) →L[ℝ] (SphereL2 →L[ℝ] SphereL2) := by
  let T : C(UnitSphere,ℝ) →ₗ[ℝ] (SphereL2 →L[ℝ] SphereL2) :=
    { toFun := sphereContinuousScalarMulL
      map_add' := by
        intro c d
        apply ContinuousLinearMap.ext
        intro u
        change sphereContinuousScalarMul (c+d) u =
          sphereContinuousScalarMul c u + sphereContinuousScalarMul d u
        apply Lp.ext
        filter_upwards [sphereContinuousScalarMul_value_ae (c+d) u,
          sphereContinuousScalarMul_value_ae c u,sphereContinuousScalarMul_value_ae d u,
          Lp.coeFn_add (sphereContinuousScalarMul c u) (sphereContinuousScalarMul d u)]
          with x hcd hc hd hadd
        rw [hcd,hadd]
        change (c x + d x) * u x = sphereContinuousScalarMul c u x + sphereContinuousScalarMul d u x
        rw [hc,hd]
        ring
      map_smul' := by
        intro t c
        apply ContinuousLinearMap.ext
        intro u
        change sphereContinuousScalarMul (t • c) u = t • sphereContinuousScalarMul c u
        apply Lp.ext
        filter_upwards [sphereContinuousScalarMul_value_ae (t • c) u,
          sphereContinuousScalarMul_value_ae c u,Lp.coeFn_smul t (sphereContinuousScalarMul c u)]
          with x htc hc hsmul
        rw [htc,hsmul]
        change (t * c x) * u x = t * sphereContinuousScalarMul c u x
        rw [hc]
        ring }
  apply T.mkContinuous 1
  intro c
  change ‖sphereContinuousScalarMulL c‖ ≤ 1 * ‖c‖
  simpa only [one_mul] using norm_sphereContinuousScalarMulL_le c

theorem sphereContinuousScalarMultiplierL_apply (c : C(UnitSphere,ℝ)) :
    sphereContinuousScalarMultiplierL c = sphereContinuousScalarMulL c := rfl

end OAI.AnisotropicCalderon.DirichletFamily
