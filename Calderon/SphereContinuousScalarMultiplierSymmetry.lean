import Calderon.SphereContinuousScalarMultiplier
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume SphereHarmonic

theorem inner_sphereContinuousScalarMulL_left
    (c : C(UnitSphere,ℝ)) (u v : SphereL2) :
    ⟪sphereContinuousScalarMulL c u,v⟫_ℝ =
      ⟪u,sphereContinuousScalarMulL c v⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sphereContinuousScalarMul_value_ae c u,
    sphereContinuousScalarMul_value_ae c v] with x hu hv
  change ⟪sphereContinuousScalarMul c u x,v x⟫_ℝ =
    ⟪u x,sphereContinuousScalarMul c v x⟫_ℝ
  rw [hu,hv]
  change ⟪c x • u x,v x⟫_ℝ = ⟪u x,c x • v x⟫_ℝ
  rw [real_inner_smul_left,real_inner_smul_right]

end OAI.AnisotropicCalderon.DirichletFamily
