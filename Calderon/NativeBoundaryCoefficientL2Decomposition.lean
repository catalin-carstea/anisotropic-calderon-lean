import Calderon.NativeBoundaryCoefficientDecomposition
import Calderon.SphereCoefficientMultiplierCLM
import Calderon.SphereContinuousScalarMultiplierProduct

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Classical
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

theorem sphereCoordinateMulL_eq_scalarMulL (i : Fin 3) :
    sphereCoordinateMulL i = sphereContinuousScalarMulL (sphereCoordinate i) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  exact (sphereCoordinateMul_value_ae i u).trans
    (sphereContinuousScalarMul_value_ae (sphereCoordinate i) u).symm

theorem sphereContinuousScalarMulL_sum_apply
    {ι : Type*} (s : Finset ι) (c : ι → C(UnitSphere,ℝ)) (u : SphereL2) :
    sphereContinuousScalarMulL (∑ i ∈ s, c i) u =
      ∑ i ∈ s, sphereContinuousScalarMulL (c i) u := by
  change sphereContinuousScalarMultiplierL (∑ i ∈ s, c i) u = _
  rw [map_sum,ContinuousLinearMap.sum_apply]
  rfl

theorem sphereContinuousScalarMulL_add_apply
    (c d : C(UnitSphere,ℝ)) (u : SphereL2) :
    sphereContinuousScalarMulL (c+d) u =
      sphereContinuousScalarMulL c u + sphereContinuousScalarMulL d u := by
  change sphereContinuousScalarMultiplierL (c+d) u = _
  rw [map_add,ContinuousLinearMap.add_apply]
  rfl

theorem boundary_coefficient_L2_decomposition
    (F : SmoothCoefficientMatrix 2) (b : Fin 3 → SphereL2) :
    (∑ i : Fin 3, ∑ j : Fin 3, sphereCoordinateMulL i
      (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F i j))) (b j))) =
    sphereContinuousScalarMulL (smoothSphereValue (boundaryNormalCoefficientData F))
        (∑ j : Fin 3, sphereCoordinateMulL j (b j)) +
      ∑ j : Fin 3, sphereContinuousScalarMulL (smoothSphereValue (boundaryTangentCoefficientData F j))
        (b j - sphereCoordinateMulL j (∑ l : Fin 3, sphereCoordinateMulL l (b l))) := by
  let a := smoothSphereValue (boundaryNormalCoefficientData F)
  let t (j : Fin 3) := smoothSphereValue (boundaryTangentCoefficientData F j)
  let r := ∑ j : Fin 3, sphereCoordinateMulL j (b j)
  have hrow (j : Fin 3) :
      (∑ i : Fin 3, sphereCoordinate i * smoothSphereValue (coefficientSmoothData (F i j))) =
        t j + a * sphereCoordinate j := by
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply,ContinuousMap.add_apply]
    change (∑ i : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val) =
      ((∑ i : Fin 3, x.val i*(coefficientSmoothData (F i j)).1 x.val) -
        (boundaryNormalCoefficientData F).1 x.val*x.val j) +
          (boundaryNormalCoefficientData F).1 x.val*x.val j
    ring
  have ht : (∑ j : Fin 3, t j * sphereCoordinate j) = 0 := by
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply,ContinuousMap.zero_apply]
    change (∑ j : Fin 3, (boundaryTangentCoefficientData F j).1 x.val*x.val j) = 0
    exact sum_boundaryTangentCoefficient_mul_coordinate_eq_zero F x
  have hcancel : (∑ j : Fin 3, sphereContinuousScalarMulL (t j) (sphereCoordinateMulL j r)) = 0 := by
    simp_rw [sphereCoordinateMulL_eq_scalarMulL,sphereContinuousScalarMulL_mul_apply]
    rw [← sphereContinuousScalarMulL_sum_apply,ht]
    change sphereContinuousScalarMultiplierL 0 r = 0
    rw [map_zero,ContinuousLinearMap.zero_apply]
  have hnormal : (∑ j : Fin 3, sphereContinuousScalarMulL (a*sphereCoordinate j) (b j)) =
      sphereContinuousScalarMulL a r := by
    simp_rw [← sphereContinuousScalarMulL_mul_apply,← sphereCoordinateMulL_eq_scalarMulL]
    rw [← map_sum]
  have hleft :
      (∑ i : Fin 3, ∑ j : Fin 3, sphereCoordinateMulL i
        (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F i j))) (b j))) =
      (∑ j : Fin 3, sphereContinuousScalarMulL (t j) (b j)) + sphereContinuousScalarMulL a r := by
    rw [Finset.sum_comm]
    simp_rw [sphereCoordinateMulL_eq_scalarMulL,sphereContinuousScalarMulL_mul_apply]
    simp_rw [← sphereContinuousScalarMulL_sum_apply,hrow,sphereContinuousScalarMulL_add_apply]
    rw [Finset.sum_add_distrib,hnormal]
  rw [hleft]
  change (∑ j : Fin 3, sphereContinuousScalarMulL (t j) (b j)) + sphereContinuousScalarMulL a r =
    sphereContinuousScalarMulL a r +
      ∑ j : Fin 3, sphereContinuousScalarMulL (t j) (b j-sphereCoordinateMulL j r)
  simp_rw [map_sub]
  rw [Finset.sum_sub_distrib,hcancel,sub_zero,add_comm]

theorem ordinaryConormalTraceL_eq_normal_add_tangent
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 F U =
      sphereContinuousScalarMulL (smoothSphereValue (boundaryNormalCoefficientData F))
        (outwardRadialTraceL hcalc τ0 U) +
      ∑ j : Fin 3, sphereContinuousScalarMulL (smoothSphereValue (boundaryTangentCoefficientData F j))
        (strongCoordinateTraceL hcalc τ0 j U -
          sphereCoordinateMulL j (outwardRadialTraceL hcalc τ0 U)) := by
  rw [ordinaryConormalTraceL_eq_sphere_coefficient_trace,boundary_coefficient_L2_decomposition]
  have hr : (∑ j : Fin 3, sphereCoordinateMulL j (strongCoordinateTraceL hcalc τ0 j U)) =
      outwardRadialTraceL hcalc τ0 U := by
    exact (outwardRadialTraceL_apply hcalc τ0 U).symm
  rw [hr]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
