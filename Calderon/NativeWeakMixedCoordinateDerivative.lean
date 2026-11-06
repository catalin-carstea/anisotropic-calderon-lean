import Calderon.NativeCoordinateTestDerivatives
import Calderon.StrongDerivativeValues
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Distributions ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem inner_testFunction_value_eq_integral
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (phi : 𝓓(ballOpens, ℝ)) :
    ⟪f,TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
      ∫ x : R3, phi x * f x := by
  rw [TauCeti.W1p.value_ofTestFunctionₗ,L2.inner_def]
  calc
    _ = ∫ x in ballOpens, phi x * f x := by
      apply integral_congr_ae
      filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 phi]
        with x hx
      rw [hx,Real.inner_apply,mul_comm]
    _ = _ := by
      simpa only [smul_eq_mul] using
        (TauCeti.setIntegral_smul_eq_integral_smul (w := (f : R3 → ℝ)) phi)

theorem nativeBallL2_ext_testFunction
    (f g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (h : ∀ phi : 𝓓(ballOpens, ℝ),
      ⟪f,TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
      ⟪g,TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ) :
    f = g := by
  have hf : LocallyIntegrableOn (f : R3 → ℝ) (ballOpens : Set R3) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable (by norm_num))
  have hg : LocallyIntegrableOn (g : R3 → ℝ) (ballOpens : Set R3) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable (by norm_num))
  have hzero := ballOpens.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.sub hg) (fun phi hphi hc hs => by
      let t : 𝓓(ballOpens, ℝ) := ⟨phi,hphi,hc,hs⟩
      have hiF := TauCeti.integrable_smul_of_locallyIntegrableOn hf t
      have hiG := TauCeti.integrable_smul_of_locallyIntegrableOn hg t
      have heq := h t
      rw [inner_testFunction_value_eq_integral,inner_testFunction_value_eq_integral] at heq
      simp only [Pi.sub_apply,smul_sub]
      change (∫ x : R3, t x • f x - t x • g x) = 0
      rw [integral_sub hiF hiG]
      change (∫ x : R3, phi x * f x) - (∫ x : R3, phi x * g x) = 0
      exact sub_eq_zero.mpr heq)
  apply Lp.ext
  rw [Filter.EventuallyEq,ae_restrict_iff' ballOpens.isOpen.measurableSet]
  filter_upwards [hzero] with x hx hxB
  exact sub_eq_zero.mp (hx hxB)

theorem unitBallCoordinateGradient_mixed_test_inner
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (i j : Fin 3)
    (phi : 𝓓(ballOpens, ℝ)) :
    ⟪unitBallCoordinateGradientL j
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)),
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi)⟫_ℝ =
    ⟪TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U),
      TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2
        (coordinateTestDerivative i (coordinateTestDerivative j phi)))⟫_ℝ := by
  rw [unitBall_coordinate_testFunction_inner_integration,
    TauCeti.Wkp.value_firstOrder,unitBallCoordinateDerivative_eq_coordinateGradient,
    ← value_coordinateTestDerivative_eq_gradient j phi,
    unitBall_coordinate_testFunction_inner_integration,neg_neg,
    ← value_coordinateTestDerivative_eq_gradient i (coordinateTestDerivative j phi)]

theorem unitBallCoordinateGradient_mixed_commute
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (i j : Fin 3) :
    unitBallCoordinateGradientL j
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)) =
      unitBallCoordinateGradientL i
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j U)) := by
  apply nativeBallL2_ext_testFunction
  intro phi
  rw [unitBallCoordinateGradient_mixed_test_inner,
    unitBallCoordinateGradient_mixed_test_inner,coordinateTestDerivative_commute i j phi]

end OAI.AnisotropicCalderon.DirichletFamily
