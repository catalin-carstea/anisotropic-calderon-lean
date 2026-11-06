import Calderon.UnitBallCoefficientOperatorSignature
import Calderon.UnitBallCoefficientFormValue

/-! EXPANSION.json precedes the exact real-value source binding for the typed operator. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem unitBallCoefficientEnergyL_apply_eq_coefficientFormL
    (C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    unitBallCoefficientEnergyL C u v = unitBallCoefficientFormL C u v := by
  rfl

theorem unitBallCoefficientEnergyL_apply_eq_energyFormH1
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    unitBallCoefficientEnergyL
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (v : BallH1) :=
  (unitBallCoefficientEnergyL_apply_eq_coefficientFormL _ u v).trans
    (unitBallCoefficientFormL_apply_eq_energyFormH1 A hcoeff u v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientEnergyL_apply_eq_coefficientFormL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientEnergyL_apply_eq_energyFormH1
