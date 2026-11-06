import Calderon.StrongCoefficientOperator
import Calderon.CoordinateWeakIntegration

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem unitBallCoordinateDerivative_eq_coordinateGradient (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i : Fin 3) (u : BallSobolev (k + 1)) :
    TauCeti.Wkp.value k (unitBallCoordinateDerivativeL hcalc k i u) =
      unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder k u) := by
  apply Lp.ext
  exact (unitBallCoordinateDerivativeL_value_ae hcalc k i u).trans
    (unitBallCoordinateGradientL_ae i (TauCeti.Wkp.firstOrder k u)).symm

theorem unitBallCoordinateDerivative_inner_integration (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i : Fin 3) (u : BallSobolev (k + 1)) (v : BallH1Zero) :
    ⟪TauCeti.Wkp.value k (unitBallCoordinateDerivativeL hcalc k i u),
      TauCeti.W1p.value (v : BallH1)⟫_ℝ =
      -⟪TauCeti.Wkp.value (k + 1) u, unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
  rw [unitBallCoordinateDerivative_eq_coordinateGradient]
  exact (unitBall_coordinate_inner_integration (TauCeti.Wkp.firstOrder k u) i v).trans
    (congrArg (fun z => -⟪z, unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ)
      (TauCeti.Wkp.value_firstOrder k u))

theorem strongCoordinateDerivative_value_ae (hcalc : FixedSobolevCalculus)
    (s : ℕ) (j : Fin 3) (u : StrongDirichletSpace s) :
    TauCeti.Wkp.value (s + 1) (strongCoordinateDerivativeL hcalc s j u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) x) j :=
  unitBallCoordinateDerivativeL_value_ae hcalc (s + 1) j (u : BallSobolev (s + 2))

theorem strongCoefficientFlux_value_ae (hcalc : FixedSobolevCalculus)
    (s : ℕ) (F : SmoothCoefficientMatrix (s + 2)) (i j : Fin 3)
    (u : StrongDirichletSpace s) :
    TauCeti.Wkp.value (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
      (strongCoordinateDerivativeL hcalc s j u))
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue (s + 2) (F i j) x *
        (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) x) j := by
  exact (coefficientMultiplier_value_ae hcalc (s + 1) (F i j)
    (strongCoordinateDerivativeL hcalc s j u)).trans
      (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _)
        (strongCoordinateDerivative_value_ae hcalc s j u))

end OAI.AnisotropicCalderon.DirichletFamily
