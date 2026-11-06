import Calderon.NativeCoefficientWeakEnergy

/-! EXPANSION.json precedes this focused actual native-dual restriction primitive. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def nativeZeroRestrictionNegL :
    (BallH1 →L[ℝ] ℝ) →L[ℝ] StrongDual ℝ BallH1Zero :=
  -((ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)

theorem nativeZeroRestrictionNegL_apply (ell : BallH1 →L[ℝ] ℝ) :
    nativeZeroRestrictionNegL ell =
      -(ell.comp (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem continuous_neg_restrict_nativeFunctionals :
    Continuous (fun ell : BallH1 →L[ℝ] ℝ =>
      -(ell.comp (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)) := by
  have hFun : (fun ell : BallH1 →L[ℝ] ℝ => nativeZeroRestrictionNegL ell) =
      (fun ell : BallH1 →L[ℝ] ℝ =>
        -(ell.comp (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)) := by
    funext ell
    exact nativeZeroRestrictionNegL_apply ell
  have hContinuous : Continuous
      (fun ell : BallH1 →L[ℝ] ℝ => nativeZeroRestrictionNegL ell) :=
    nativeZeroRestrictionNegL.continuous
  have hPred : Continuous (fun ell : BallH1 →L[ℝ] ℝ => nativeZeroRestrictionNegL ell) =
      Continuous (fun ell : BallH1 →L[ℝ] ℝ =>
        -(ell.comp (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)) :=
    congrArg (fun F : (BallH1 →L[ℝ] ℝ) → StrongDual ℝ BallH1Zero => Continuous F) hFun
  exact Eq.mp hPred hContinuous

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroRestrictionNegL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroRestrictionNegL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_neg_restrict_nativeFunctionals
