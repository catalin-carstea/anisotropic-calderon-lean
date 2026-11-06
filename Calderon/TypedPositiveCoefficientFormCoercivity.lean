import Calderon.PositiveCoefficientScalarNativeCoercivity
import Calderon.UnitBallCoefficientOperatorValueBinding
import Calderon.ScalarEnergyCoercivityTransport
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem isCoercive_unitBallCoefficientEnergyL_positiveCoefficient
    (A : MatrixField) (hA : Continuous A) (hPos : ∀ x, (A x).PosDef)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    IsCoercive (unitBallCoefficientEnergyL
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)))) := by
  let C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
  let B : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := unitBallCoefficientEnergyL C
  let E : BallH1Zero → BallH1Zero → ℝ := fun u v =>
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (v : BallH1)
  have hLower := exists_positiveCoefficient_native_energy_lower_bound A hA hPos
  have hValue : ∀ u : BallH1Zero, B u u = E u u :=
    fun u => unitBallCoefficientEnergyL_apply_eq_energyFormH1 A hcoeff u u
  exact isCoercive_of_scalar_energy_lower_bound B E hValue hLower

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isCoercive_unitBallCoefficientEnergyL_positiveCoefficient
