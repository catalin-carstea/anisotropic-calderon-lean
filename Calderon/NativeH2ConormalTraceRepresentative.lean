import Calderon.NativeCoefficientFluxTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic

lemma sphereCoordinate_coefficient_mul_value_ae
    (i : Fin 3) (F : SmoothCoefficientJets 2) (v : SphereL2) :
    sphereCoordinateMulL i (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) v)
      =ᵐ[sphereProbability] fun x : UnitSphere => x.val i * coefficientValue 2 F x.val * v x := by
  filter_upwards [sphereCoordinateMul_value_ae i
    (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) v),
    sphereContinuousScalarMul_value_ae (smoothSphereValue (coefficientSmoothData F)) v] with x hc hm
  change _ = x.val i * coefficientValue 2 F x.val * v x
  change sphereCoordinateMulL i (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) v) x =
    sphereCoordinate i x * sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) v x at hc
  change sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) v x =
    smoothSphereValue (coefficientSmoothData F) x * v x at hm
  rw [hc,hm]
  exact (mul_assoc _ _ _).symm

lemma ordinaryConormalTraceL_value_ae
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 F U =ᵐ[sphereProbability] fun x : UnitSphere =>
      ∑ i : Fin 3, ∑ j : Fin 3, x.val i * coefficientMatrixField 2 F x.val i j *
        strongCoordinateTraceL hcalc τ0 j U x := by
  rw [ordinaryConormalTraceL_eq_sphere_coefficient_trace]
  have hrow (i : Fin 3) :
      (∑ j : Fin 3, sphereCoordinateMulL i (sphereContinuousScalarMulL
        (smoothSphereValue (coefficientSmoothData (F i j))) (strongCoordinateTraceL hcalc τ0 j U)))
      =ᵐ[sphereProbability] fun x : UnitSphere => ∑ j : Fin 3,
        x.val i * coefficientValue 2 (F i j) x.val * strongCoordinateTraceL hcalc τ0 j U x :=
    (Lp.coeFn_finsetSum Finset.univ _).trans
      (eventuallyEq_sum fun j _ => sphereCoordinate_coefficient_mul_value_ae i (F i j) _)
  exact (Lp.coeFn_finsetSum Finset.univ _).trans (eventuallyEq_sum fun i _ => hrow i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereCoordinate_coefficient_mul_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_value_ae
