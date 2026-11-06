import Calderon.UnitBallFullCoefficientEnergyIdentity
import Calderon.NativeAffineBilinearContinuity
import Calderon.CoefficientFormJointContinuity
import Calderon.CoefficientFormScalarEvaluation
import Calderon.NativeCoefficientWeakEnergy
import Calderon.NativeZeroRestrictionNegation

/-! EXPANSION.json precedes the actual full coefficient energy and affine RHS bridge.
The selected density route keeps the smooth boundary datum fixed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def unitBallFullCoefficientFormL :=
  coefficientFormL (J := ℝ × R3) ((volume : Measure R3).restrict ballOpens)
    (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens))

theorem unitBallFullCoefficientFormL_apply_eq_energyFormH1
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) :
    unitBallFullCoefficientFormL
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) u v := by
  exact coefficientFormL_jetLpL_apply_eq_energyFormH1 A hcoeff u v

def unitBallCoefficientAffineForcing
    (C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) (d : BallH1) : StrongDual ℝ BallH1Zero :=
  -((unitBallFullCoefficientFormL C d).comp
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL)

theorem continuous_unitBallCoefficientAffineForcing :
    Continuous (fun p :
      Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
        ((volume : Measure R3).restrict ballOpens) × BallH1 =>
      unitBallCoefficientAffineForcing p.1 p.2) := by
  have hFull := continuous_coefficientFormL_uncurry (J := ℝ × R3)
    ((volume : Measure R3).restrict ballOpens)
    (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens))
  have hNative := continuous_neg_restrict_nativeFunctionals.comp hFull
  exact hNative

theorem unitBallCoefficientAffineForcing_apply_eq_neg_energyFormH1
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (d : BallH1) (v : BallH1Zero) :
    unitBallCoefficientAffineForcing
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) d v =
      -TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) d (v : BallH1) := by
  have hFull := unitBallFullCoefficientFormL_apply_eq_energyFormH1 A hcoeff d (v : BallH1)
  have hApply : unitBallCoefficientAffineForcing
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) d v =
      -(unitBallFullCoefficientFormL
        (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
          ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) d (v : BallH1)) := rfl
  exact hApply.trans (congrArg (fun r : ℝ => -r) hFull)

theorem unitBallCoefficientAffineForcing_eq_native
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (d : BallH1) :
    unitBallCoefficientAffineForcing
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) d =
      -(nativeCoefficientWeakEnergyL A (0 : R3 → R3) (0 : R3 → ℝ) hcoeff d) := by
  apply ContinuousLinearMap.ext
  intro v
  have hRhs : (-(nativeCoefficientWeakEnergyL A (0 : R3 → R3) (0 : R3 → ℝ) hcoeff d)) v =
      -TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) d (v : BallH1) := by
    rw [ContinuousLinearMap.neg_apply,nativeCoefficientWeakEnergyL_apply]
  exact (unitBallCoefficientAffineForcing_apply_eq_neg_energyFormH1 A hcoeff d v).trans hRhs.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallFullCoefficientFormL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallFullCoefficientFormL_apply_eq_energyFormH1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientAffineForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_unitBallCoefficientAffineForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientAffineForcing_apply_eq_neg_energyFormH1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientAffineForcing_eq_native
