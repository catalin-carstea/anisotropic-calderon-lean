import Calderon.NativeSupportedAdjointStrongForcing
import Calderon.NativeCoefficientMultiplierOrderCoherence
import Calderon.NativeSmoothMultiplierForcingCoefficients

/-! Gain of the high smooth multiplier: the native H2→H1 forcing, with the same low graph. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

attribute [local irreducible] nativeH2FirstOrderL coefficientMultiplier nativeCoefficientH1ProductL
  unitBallCoordinateDerivativeL unitBallCoordinateGradientL


def nativeHighSmoothMultiplierForcingL (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1) :
    BallSobolev 2 →L[ℝ] BallSobolev 1 :=
  let column : Fin 3 → BallSobolev 2 →L[ℝ] BallSobolev 1 := fun i =>
    (unitBallCoordinateDerivativeL hcalc 1 i).comp
      (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 (C i)))
  let row : Fin 3 → BallSobolev 2 →L[ℝ] BallSobolev 1 := fun j =>
    (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (R j))).comp
      (unitBallCoordinateDerivativeL hcalc 1 j)
  let drift : BallSobolev 2 →L[ℝ] BallSobolev 1 :=
    (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 d)).comp
      nativeH2FirstOrderL
  (∑ i : Fin 3, column i) + (∑ j : Fin 3, row j) - drift


lemma nativeHighSmoothMultiplierForcingL_apply (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1) (U : BallSobolev 2) :
    nativeHighSmoothMultiplierForcingL hcalc C R d U =
      (∑ i : Fin 3, unitBallCoordinateDerivativeL hcalc 1 i
        (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 (C i)) U)) +
      (∑ j : Fin 3, coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (R j))
        (unitBallCoordinateDerivativeL hcalc 1 j U)) -
      coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 d) (TauCeti.Wkp.lowerOrder 1 U) := by
  let M : BallSobolev 1 →L[ℝ] BallSobolev 1 :=
    coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 d)
  have hComp : (M.comp nativeH2FirstOrderL) U = M (nativeH2FirstOrderL U) := rfl
  have hFirst : nativeH2FirstOrderL U = TauCeti.Wkp.lowerOrder 1 U :=
    nativeH2FirstOrderL_apply U
  have hDrift : (M.comp nativeH2FirstOrderL) U = M (TauCeti.Wkp.lowerOrder 1 U) :=
    hComp.trans (congrArg M hFirst)
  simp only [nativeHighSmoothMultiplierForcingL,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  exact congrArg (fun z : BallSobolev 1 =>
    (∑ i : Fin 3, unitBallCoordinateDerivativeL hcalc 1 i
      (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 (C i)) U)) +
    (∑ j : Fin 3, coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (R j))
      (unitBallCoordinateDerivativeL hcalc 1 j U)) - z) hDrift


lemma value_nativeHighSmoothMultiplierForcingL (hcalc : FixedSobolevCalculus)
    (C : Fin 3 → SmoothCoefficientJets 2)
    (R : Fin 3 → SmoothCoefficientJets 1) (d : SmoothCoefficientJets 1) (U : BallSobolev 2) :
    TauCeti.Wkp.value 1 (nativeHighSmoothMultiplierForcingL hcalc C R d U) =
      nativeSmoothMultiplierForcingL hcalc C R d (TauCeti.Wkp.firstOrder 1 U) := by
  let v := TauCeti.Wkp.firstOrder 1 U
  have hColumn (i : Fin 3) :
      TauCeti.Wkp.value 1 (unitBallCoordinateDerivativeL hcalc 1 i
        (coefficientMultiplier hcalc 2 (coefficientRepackedJets 2 3 (C i)) U)) =
      unitBallCoordinateGradientL i (nativeCoefficientH1ProductL hcalc (C i) v) :=
    (value_unitBallCoordinateDerivativeL_one hcalc i _).trans
      (congrArg (unitBallCoordinateGradientL i)
        (firstOrder_repackedCoefficientMultiplier_two hcalc (C i) U))
  have hRow (j : Fin 3) :
      TauCeti.Wkp.value 1
        (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 (R j))
          (unitBallCoordinateDerivativeL hcalc 1 j U)) =
      coefficientMultiplier hcalc 0 (R j) (unitBallCoordinateGradientL j v) :=
    (lowerOrder_coefficientMultiplier_of_value_eq hcalc 0
      (coefficientRepackedJets 1 2 (R j)) (R j) (coefficientValue_repackedJets 1 2 (R j)) _).trans
      (congrArg (coefficientMultiplier hcalc 0 (R j))
        (value_unitBallCoordinateDerivativeL_one hcalc j U))
  have hDrift :
      TauCeti.Wkp.value 1
        (coefficientMultiplier hcalc 1 (coefficientRepackedJets 1 2 d) (TauCeti.Wkp.lowerOrder 1 U)) =
      coefficientMultiplier hcalc 0 d (TauCeti.W1p.value v) :=
    lowerOrder_coefficientMultiplier_of_value_eq hcalc 0
      (coefficientRepackedJets 1 2 d) d (coefficientValue_repackedJets 1 2 d) _
  rw [nativeHighSmoothMultiplierForcingL_apply,nativeSmoothMultiplierForcingL_apply]
  change (TauCeti.Wkp.valueL 1) (_+_-_) = _
  simp only [map_sub,map_add,map_sum,TauCeti.Wkp.valueL_apply]
  exact congrArg₂ (fun x y : BallSobolev 0 => x-y)
    (congrArg₂ (fun x y : BallSobolev 0 => x+y)
      (Finset.sum_congr rfl (fun i _ => hColumn i))
      (Finset.sum_congr rfl (fun j _ => hRow j))) hDrift

def nativeHighBulkMultiplierCommutatorForcingL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (G : Fin 3 → SmoothCoefficientJets 1)
    (Q : SmoothCoefficientJets 3) : BallSobolev 2 →L[ℝ] BallSobolev 1 :=
  nativeHighSmoothMultiplierForcingL hcalc (smoothMultiplierColumnJets F Q)
    (smoothMultiplierRowJets F Q) (smoothMultiplierDriftJets G Q)

lemma value_nativeHighBulkMultiplierCommutatorForcingL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (G : Fin 3 → SmoothCoefficientJets 1)
    (Q : SmoothCoefficientJets 3) (U : BallSobolev 2) :
    TauCeti.Wkp.value 1 (nativeHighBulkMultiplierCommutatorForcingL hcalc F G Q U) =
      nativeBulkMultiplierCommutatorForcingL hcalc F G Q (TauCeti.Wkp.firstOrder 1 U) :=
  value_nativeHighSmoothMultiplierForcingL hcalc
    (smoothMultiplierColumnJets F Q) (smoothMultiplierRowJets F Q) (smoothMultiplierDriftJets G Q) U

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighSmoothMultiplierForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighSmoothMultiplierForcingL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeHighSmoothMultiplierForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHighBulkMultiplierCommutatorForcingL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeHighBulkMultiplierCommutatorForcingL

