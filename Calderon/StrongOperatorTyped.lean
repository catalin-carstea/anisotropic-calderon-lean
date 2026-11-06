import Calderon.StrongCoefficientOperator
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def strongDirichletOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  strongCoefficientOperatorL hcalc s F

theorem strongDirichletOperator_eq (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) :
    strongDirichletOperator hcalc s F = strongCoefficientOperatorL hcalc s F := rfl

theorem strongDirichletOperator_apply (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (u : StrongDirichletSpace s) :
    strongDirichletOperator hcalc s F u =
      -∑ i, ∑ j, unitBallCoordinateDerivativeL hcalc s i
        (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)) :=
  strongCoefficientOperatorL_apply_apply hcalc s F u

end OAI.AnisotropicCalderon.DirichletFamily
