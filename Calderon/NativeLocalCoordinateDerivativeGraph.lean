import Calderon.NativeSmoothCoordinateDerivative
import TauCeti.Analysis.Sobolev.Wkp.Classical

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

/-- The original fixed Sobolev derivative has the classical local representative. -/
theorem unitBallCoordinateDerivativeL_value_ae_of_contDiffOn
    (hcalc : FixedSobolevCalculus) (k : ℕ) (i : Fin 3)
    (U : BallSobolev (k + 1)) (f : R3 → ℝ)
    (hf : ContDiffOn ℝ ∞ f ballOpens)
    (hU : (TauCeti.Wkp.value (k + 1) U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f) :
    (TauCeti.Wkp.value k (unitBallCoordinateDerivativeL hcalc k i U) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => fderiv ℝ f x (coordinateVector i) := by
  let v := TauCeti.Wkp.firstOrder k U
  have hValue : (TauCeti.Wkp.value 1 v : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] f := by
    have hProjection : TauCeti.Wkp.value 1 v = TauCeti.Wkp.value (k + 1) U :=
      (TauCeti.Wkp.value_one v).trans (TauCeti.Wkp.value_firstOrder k U)
    filter_upwards [hU] with x hx
    exact (congrArg (fun z : BallSobolev 0 => z x) hProjection).trans hx
  have hGradient := TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn 0 v
    (hf.of_le (by simp)) hValue
  have hDerivative := unitBallCoordinateDerivativeL_value_ae hcalc k i U
  filter_upwards [hDerivative, hGradient] with x hx hy
  have hGradientPoint : TauCeti.W1p.gradient v x = gradient f x := by
    have hy' : (TauCeti.Wkp.iteratedGradient 0 v : R3 → R3) x = gradient f x := hy
    have hProjection := congrArg
      (fun z : Lp R3 2 ((volume : Measure R3).restrict ballOpens) => z x)
      (TauCeti.Wkp.iteratedGradient_zero v)
    exact hProjection.symm.trans hy'
  have hCoordinate := (congrArg (fun z : R3 => z i) hGradientPoint).trans
    (gradient_coordinate f x i)
  exact hx.trans hCoordinate

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoordinateDerivativeL_value_ae_of_contDiffOn
