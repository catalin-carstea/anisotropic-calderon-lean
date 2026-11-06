import Calderon.DivergenceOperatorFamily
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- The coordinate derivative on the actual fixed Tau graph spaces. -/
def unitBallCoordinateDerivativeL (hcalc : FixedSobolevCalculus) (k : ℕ) (i : Fin 3) :=
  Classical.choose (hcalc.2 k i)

theorem unitBallCoordinateDerivativeL_value_ae (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i : Fin 3) (u : BallSobolev (k + 1)) :
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
      (unitBallCoordinateDerivativeL hcalc k i u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => (TauCeti.W1p.gradient (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (TauCeti.Wkp.firstOrder k u) x) i :=
  Classical.choose_spec (hcalc.2 k i) u

/-- Strong-domain assembly using precisely the actual coordinate derivatives. -/
def unitBallDivergenceL (hcalc : FixedSobolevCalculus) (s : ℕ) :=
  coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
    (fun j => (unitBallCoordinateDerivativeL hcalc (s + 1) j).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL)

end OAI.AnisotropicCalderon.DirichletFamily
