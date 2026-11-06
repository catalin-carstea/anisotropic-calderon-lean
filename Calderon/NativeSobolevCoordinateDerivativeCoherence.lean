import Calderon.NativeSmoothCoordinateDerivative

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-H3-TRACE-EXPANSION-v001.md, Component A. Actual value graphs force lowering coherence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

attribute [local irreducible] unitBallCoordinateDerivativeL

theorem lowerOrder_unitBallCoordinateDerivativeL
    (hcalc : FixedSobolevCalculus) (n : ℕ) (i : Fin 3) (U : BallSobolev (n+2)) :
    TauCeti.Wkp.lowerOrder n (unitBallCoordinateDerivativeL hcalc (n+1) i U) =
      unitBallCoordinateDerivativeL hcalc n i (TauCeti.Wkp.lowerOrder (n+1) U) := by
  apply TauCeti.Wkp.ext n
  rw [← TauCeti.Wkp.value_succ]
  apply Lp.ext
  filter_upwards [unitBallCoordinateDerivativeL_value_ae hcalc (n+1) i U,
    unitBallCoordinateDerivativeL_value_ae hcalc n i (TauCeti.Wkp.lowerOrder (n+1) U)]
    with x hHigh hLow
  simpa only [TauCeti.Wkp.firstOrder_succ] using hHigh.trans hLow.symm

theorem firstOrder_unitBallCoordinateDerivativeL_H3
    (hcalc : FixedSobolevCalculus) (i : Fin 3) (U : BallSobolev 3) :
    TauCeti.Wkp.firstOrder 1 (unitBallCoordinateDerivativeL hcalc 2 i U) =
      unitBallCoordinateDerivativeL hcalc 1 i (TauCeti.Wkp.lowerOrder 2 U) := by
  calc
    _ = TauCeti.Wkp.lowerOrder 1 (unitBallCoordinateDerivativeL hcalc 2 i U) := rfl
    _ = _ := lowerOrder_unitBallCoordinateDerivativeL hcalc 1 i U

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.lowerOrder_unitBallCoordinateDerivativeL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.firstOrder_unitBallCoordinateDerivativeL_H3
