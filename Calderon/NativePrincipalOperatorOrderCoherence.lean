import Calderon.OrdinaryWeightedDriftOperator
import Calderon.NativeCoefficientMultiplierOrderCoherence
import Calderon.StrongHarmonicProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem lowerOrder_ordinaryPrincipalL_of_value_eq
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientMatrix (k+3)) (G : SmoothCoefficientMatrix (k+2))
    (hFG : ∀ i j, coefficientValue (k+3) (F i j) = coefficientValue (k+2) (G i j))
    (U : BallSobolev (k+3)) :
    TauCeti.Wkp.lowerOrder k (ordinaryPrincipalL hcalc (k+1) F U) =
      ordinaryPrincipalL hcalc k G (TauCeti.Wkp.lowerOrder (k+2) U) := by
  rw [ordinaryPrincipalL_apply,ordinaryPrincipalL_apply]
  rw [← TauCeti.Wkp.lowerOrderL_apply k]
  simp only [map_neg,map_sum]
  apply congrArg Neg.neg
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  change TauCeti.Wkp.lowerOrder k
    (unitBallCoordinateDerivativeL hcalc (k+1) i
      (coefficientMultiplier hcalc (k+2) (F i j)
        (unitBallCoordinateDerivativeL hcalc (k+2) j U))) = _
  rw [lowerOrder_unitBallCoordinateDerivativeL]
  rw [lowerOrder_coefficientMultiplier_of_value_eq hcalc (k+1) (F i j) (G i j)
    (hFG i j)]
  rw [lowerOrder_unitBallCoordinateDerivativeL]

theorem ordinaryPrincipalL_lowerOrder_eq_zero_of_high_eq_zero
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientMatrix (k+3)) (G : SmoothCoefficientMatrix (k+2))
    (hFG : ∀ i j, coefficientValue (k+3) (F i j) = coefficientValue (k+2) (G i j))
    (U : BallSobolev (k+3)) (hU : ordinaryPrincipalL hcalc (k+1) F U = 0) :
    ordinaryPrincipalL hcalc k G (TauCeti.Wkp.lowerOrder (k+2) U) = 0 := by
  rw [← lowerOrder_ordinaryPrincipalL_of_value_eq hcalc k F G hFG U,hU,
    ← TauCeti.Wkp.lowerOrderL_apply k,map_zero]

theorem ordinaryPrincipalL_lowerOrder_strongHarmonicProjectionL_eq_zero
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientMatrix (k+3)) (G : SmoothCoefficientMatrix (k+2))
    (hFG : ∀ i j, coefficientValue (k+3) (F i j) = coefficientValue (k+2) (G i j))
    (hi : ((ordinaryPrincipalL hcalc (k+1) F).comp
      (strongDirichletSubmodule (k+1)).toSubmodule.subtypeL).IsInvertible)
    (U : BallSobolev (k+3)) :
    ordinaryPrincipalL hcalc k G
      (TauCeti.Wkp.lowerOrder (k+2)
        (strongHarmonicProjectionL (k+1) (ordinaryPrincipalL hcalc (k+1) F) U)) = 0 := by
  exact ordinaryPrincipalL_lowerOrder_eq_zero_of_high_eq_zero hcalc k F G hFG _
    (strongHarmonicProjectionL_equation (k+1) (ordinaryPrincipalL hcalc (k+1) F) hi U)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
