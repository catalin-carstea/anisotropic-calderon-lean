import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.NativeSobolevCoordinateDerivativeCoherence

/-! Equal values force finite-order coherence of the native coefficient multipliers. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def coefficientRepackedJets (r s : ℕ) (F : SmoothCoefficientJets r) : SmoothCoefficientJets s :=
  compactCoefficient s (coefficientValue r F) (contDiff_coefficientValue r F)
    (hasCompactSupport_coefficientValue r F)

lemma coefficientValue_repackedJets (r s : ℕ) (F : SmoothCoefficientJets r) :
    coefficientValue s (coefficientRepackedJets r s F) = coefficientValue r F :=
  coefficientValue_compactCoefficient s _ _ _

attribute [local irreducible] coefficientMultiplier nativeCoefficientH1ProductL
  unitBallCoordinateDerivativeL unitBallCoordinateGradientL

lemma lowerOrder_coefficientMultiplier_of_value_eq (hcalc : FixedSobolevCalculus)
    (k : ℕ) (F : SmoothCoefficientJets (k+2)) (G : SmoothCoefficientJets (k+1))
    (hFG : coefficientValue (k+2) F = coefficientValue (k+1) G) (U : BallSobolev (k+1)) :
    TauCeti.Wkp.lowerOrder k (coefficientMultiplier hcalc (k+1) F U) =
      coefficientMultiplier hcalc k G (TauCeti.Wkp.lowerOrder k U) := by
  apply TauCeti.Wkp.ext k
  rw [← TauCeti.Wkp.value_succ]
  apply Lp.ext
  have hU := TauCeti.Wkp.value_succ k U
  have hHigh := coefficientMultiplier_value_ae hcalc (k+1) F U
  rw [hFG,hU] at hHigh
  exact hHigh.trans (coefficientMultiplier_value_ae hcalc k G (TauCeti.Wkp.lowerOrder k U)).symm

lemma value_unitBallCoordinateDerivativeL_one (hcalc : FixedSobolevCalculus)
    (i : Fin 3) (U : BallSobolev 2) :
    TauCeti.Wkp.value 1 (unitBallCoordinateDerivativeL hcalc 1 i U) =
      unitBallCoordinateGradientL i (TauCeti.Wkp.firstOrder 1 U) := by
  apply Lp.ext
  exact (unitBallCoordinateDerivativeL_value_ae hcalc 1 i U).trans
    (unitBallCoordinateGradientL_ae i (TauCeti.Wkp.firstOrder 1 U)).symm

lemma firstOrder_repackedCoefficientMultiplier_two (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientJets 2) (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1
      (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 F) U) =
      nativeCoefficientH1ProductL hcalc F (TauCeti.Wkp.firstOrder 1 U) := by
  have h := lowerOrder_coefficientMultiplier_of_value_eq hcalc 1
    (coefficientRepackedJets 2 3 F) F (coefficientValue_repackedJets 2 3 F) U
  unfold nativeCoefficientH1ProductL
  exact h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientRepackedJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_repackedJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lowerOrder_coefficientMultiplier_of_value_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_unitBallCoordinateDerivativeL_one
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_repackedCoefficientMultiplier_two

