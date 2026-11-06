import Calderon.TypedDilatedCoefficientEnergyContinuity
import Calderon.TypedPositiveCoefficientNativeCorrection
import Calderon.UnitBallCoefficientAffineForcing
import Calderon.TypedPositiveCoefficientFormCoercivity

/-! EXPANSION.json precedes these smaller actual radius-energy and solver-binding leaves. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] positiveCoefficientDirichletCorrection
  dilatedCoefficientNativeEnergy unitBallCoefficientEnergyL unitBallCoefficientAffineForcing
  nativeZeroFunctionalInverse

theorem isCoercive_dilatedCoefficientNativeEnergy_positive
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (R : ℝ) :
    IsCoercive (dilatedCoefficientNativeEnergy A hA.continuous R) := by
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: coercivity proof entered"
  let AR : MatrixField := fun x => A (R • x)
  have hAR : ContDiff ℝ ∞ AR := hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff
  let hc := memLp_continuousCoefficientEnergyIntegrand AR hAR.continuous
  have hC : dilatedCoefficientEnergyLp A hA.continuous R = hc.toLp
      (fun x => TauCeti.PDE.energyIntegrand (AR x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) := rfl
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: coercivity coefficient binding done"
  have hE : dilatedCoefficientNativeEnergy A hA.continuous R =
      unitBallCoefficientEnergyL (hc.toLp (fun x => TauCeti.PDE.energyIntegrand (AR x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) := by
    unfold dilatedCoefficientNativeEnergy
    exact congrArg unitBallCoefficientEnergyL hC
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: coercivity energy binding done"
  exact hE.symm ▸ isCoercive_unitBallCoefficientEnergyL_positiveCoefficient
    AR hAR.continuous (fun x => hPos (R • x)) hc

theorem dilatedPositiveCoefficientCorrection_eq_native_inverse
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef)
    (f : SmoothData) (R : ℝ) :
    positiveCoefficientDirichletCorrection (fun x => A (R • x))
      (hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff) (fun x => hPos (R • x)) f =
      nativeZeroFunctionalInverse (dilatedCoefficientNativeEnergy A hA.continuous R)
        (unitBallCoefficientAffineForcing (dilatedCoefficientEnergyLp A hA.continuous R)
          (smoothSobolev f)) := by
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: inverse binding proof entered"
  let AR : MatrixField := fun x => A (R • x)
  have hAR : ContDiff ℝ ∞ AR := hA.comp (R • ContinuousLinearMap.id ℝ R3).contDiff
  let hc := memLp_continuousCoefficientEnergyIntegrand AR hAR.continuous
  let C := dilatedCoefficientEnergyLp A hA.continuous R
  let E : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero := dilatedCoefficientNativeEnergy A hA.continuous R
  let ell : StrongDual ℝ BallH1Zero := unitBallCoefficientAffineForcing C (smoothSobolev f)
  have hC : C = hc.toLp (fun x => TauCeti.PDE.energyIntegrand (AR x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) := rfl
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: inverse coefficient binding done"
  have hEnergy : E = unitBallCoefficientEnergyL
      (hc.toLp (fun x => TauCeti.PDE.energyIntegrand (AR x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) := by
    dsimp only [E]
    unfold dilatedCoefficientNativeEnergy
    exact congrArg unitBallCoefficientEnergyL hC
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: inverse energy binding done"
  have hEll : ell = -(nativeCoefficientWeakEnergyL AR (0 : R3 → R3) (0 : R3 → ℝ) hc
      (smoothSobolev f)) := by
    dsimp only [ell]
    rw [hC]
    exact unitBallCoefficientAffineForcing_eq_native AR hc (smoothSobolev f)
  run_tac Lean.logInfo m!"ActualDilatedNativeCorrectionBinding: inverse forcing binding done"
  calc
    _ = coefficientFormDirichletCorrection AR hAR (fun x => hPos (R • x)) f :=
      (coefficientFormDirichletCorrection_eq_native AR hAR (fun x => hPos (R • x)) f).symm
    _ = nativeZeroFunctionalInverse
        (unitBallCoefficientEnergyL (hc.toLp (fun x => TauCeti.PDE.energyIntegrand (AR x)
          ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))))
        (-(nativeCoefficientWeakEnergyL AR (0 : R3 → R3) (0 : R3 → ℝ) hc (smoothSobolev f))) := by
      unfold coefficientFormDirichletCorrection unitBallCoefficientNativeInverse
      rfl
    _ = nativeZeroFunctionalInverse E
        (-(nativeCoefficientWeakEnergyL AR (0 : R3 → R3) (0 : R3 → ℝ) hc (smoothSobolev f))) :=
      congrArg (fun P : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero =>
        nativeZeroFunctionalInverse P
          (-(nativeCoefficientWeakEnergyL AR (0 : R3 → R3) (0 : R3 → ℝ) hc (smoothSobolev f))))
        hEnergy.symm
    _ = _ := congrArg (nativeZeroFunctionalInverse E) hEll.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isCoercive_dilatedCoefficientNativeEnergy_positive
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dilatedPositiveCoefficientCorrection_eq_native_inverse
