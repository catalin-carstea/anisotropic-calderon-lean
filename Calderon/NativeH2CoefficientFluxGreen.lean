import Calderon.NativeH1CoordinateBoundaryGreen
import Calderon.OrdinaryWeightedDriftOperator
import Calderon.StrongDerivativeValues

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativePolynomialBulkMoments NativeH1CoordinateBoundaryGreen

/-! Expanded before source in EXPANSION-native-H2-coefficient-flux-Green-v001.json. -/

def ordinaryConormalTraceL (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) : BallSobolev 2 →L[ℝ] SphereL2 :=
  ∑ i : Fin 3, ∑ j : Fin 3, (sphereCoordinateMulL i).comp
    (τ0.valueTraceL.comp ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0).comp
        ((coefficientMultiplier hcalc 1 (F i j)).comp (unitBallCoordinateDerivativeL hcalc 1 j))))

lemma ordinaryConormalTraceL_apply (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 F U = ∑ i : Fin 3, ∑ j : Fin 3,
      sphereCoordinateMulL i (τ0.valueTraceL (TauCeti.Wkp.firstOrder 0
        (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U)))) := by
  simp only [ordinaryConormalTraceL,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun u : BallH1 => sphereCoordinateMulL i (τ0.valueTraceL u))
    (TauCeti.Wkp.firstOrderL_apply (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0
        (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U)))

lemma inner_value_ordinaryPrincipalL_eq_neg_flux_derivative
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (U : BallSobolev 2) (v : BallH1) :
    ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),TauCeti.W1p.value v⟫_ℝ =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ⟪unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder 0
          (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U))),
            TauCeti.W1p.value v⟫_ℝ := by
  rw [ordinaryPrincipalL_apply]
  change ⟪TauCeti.Wkp.valueL 0 (-∑ i : Fin 3, ∑ j : Fin 3,
    unitBallCoordinateDerivativeL hcalc 0 i
      (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U))),
        TauCeti.W1p.value v⟫_ℝ = _
  simp only [map_neg,map_sum,inner_neg_left,sum_inner]
  apply congrArg (fun t : ℝ => -t)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hd : TauCeti.Wkp.valueL 0
      (unitBallCoordinateDerivativeL hcalc 0 i
        (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U))) =
      unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder 0
        (coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U))) :=
    unitBallCoordinateDerivative_eq_coordinateGradient hcalc 0 i _
  exact congrArg (fun z : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
    ⟪z,TauCeti.W1p.value v⟫_ℝ) hd

lemma ordinaryPrincipalL_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (U : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) v =
        ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),TauCeti.W1p.value v⟫_ℝ +
          sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ := by
  let Q (i j : Fin 3) : BallSobolev 1 :=
    coefficientMultiplier hcalc 1 (F i j) (unitBallCoordinateDerivativeL hcalc 1 j U)
  have hE := energyFormH1_eq_sum_coordinateFlux_inner (coefficientMatrixField 2 F)
    (TauCeti.Wkp.firstOrder 1 U) v (fun i j => TauCeti.Wkp.value 1 (Q i j))
      (fun i j => ordinaryCoefficientFlux_value_ae hcalc 0 F i j U)
  have hP := inner_value_ordinaryPrincipalL_eq_neg_flux_derivative hcalc F U v
  have hB : sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ =
      ∑ i : Fin 3, ∑ j : Fin 3, sphereSurfaceMass *
        ⟪sphereCoordinateMulL i (τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (Q i j))),τ0.valueTraceL v⟫_ℝ := by
    rw [ordinaryConormalTraceL_apply]
    simp only [sum_inner,Finset.mul_sum,Q]
  have hterm (i j : Fin 3) :
      ⟪TauCeti.Wkp.value 1 (Q i j),unitBallCoordinateGradientL i v⟫_ℝ =
        sphereSurfaceMass * ⟪sphereCoordinateMulL i
          (τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (Q i j))),τ0.valueTraceL v⟫_ℝ -
        ⟪unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder 0 (Q i j)),TauCeti.W1p.value v⟫_ℝ := by
    have h := unitBall_coordinate_boundary_inner τ0 (TauCeti.Wkp.firstOrder 0 (Q i j)) v i
    rw [TauCeti.Wkp.value_firstOrder] at h
    linarith
  rw [hE]
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib]
  rw [← hB]
  change sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ -
    (∑ i : Fin 3, ∑ j : Fin 3, ⟪unitBallCoordinateGradientL i
      (TauCeti.Wkp.firstOrder 0 (Q i j)),TauCeti.W1p.value v⟫_ℝ) = _
  change ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),TauCeti.W1p.value v⟫_ℝ =
    -(∑ i : Fin 3, ∑ j : Fin 3, ⟪unitBallCoordinateGradientL i
      (TauCeti.Wkp.firstOrder 0 (Q i j)),TauCeti.W1p.value v⟫_ℝ) at hP
  linarith

lemma ordinaryPrincipalL_harmonic_full_test_energy
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (U : BallSobolev 2) (hU : ordinaryPrincipalL hcalc 0 F U = 0) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) v =
        sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ := by
  rw [ordinaryPrincipalL_full_test_energy_Green hcalc τ0 F U v,hU]
  simp only [TauCeti.Wkp.value_zero,_root_.inner_zero_left,zero_add]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.inner_value_ordinaryPrincipalL_eq_neg_flux_derivative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_full_test_energy_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_harmonic_full_test_energy
