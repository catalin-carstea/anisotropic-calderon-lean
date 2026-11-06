import Calderon.NativeSmoothCoordinateDerivative
import Calderon.CoordinateWeakIntegration
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Distributions ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

theorem smoothCoordinateDerivative_commute (f : SmoothData) (i j : Fin 3) :
    smoothCoordinateDerivative (smoothCoordinateDerivative f j) i =
      smoothCoordinateDerivative (smoothCoordinateDerivative f i) j := by
  apply Subtype.ext
  funext x
  have hf : DifferentiableAt ℝ (fderiv ℝ f.1) x :=
    (f.2.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ f.1 y (coordinateVector j)) x (coordinateVector i) =
    fderiv ℝ (fun y => fderiv ℝ f.1 y (coordinateVector i)) x (coordinateVector j)
  rw [derivative_covector_entry f.1 x (coordinateVector i) hf j,
    derivative_covector_entry f.1 x (coordinateVector j) hf i]
  exact f.2.contDiffAt.isSymmSndFDerivAt (by simp) _ _

def coordinateTestDerivative (i : Fin 3) (phi : 𝓓(ballOpens, ℝ)) : 𝓓(ballOpens, ℝ) :=
  TestFunction.lineDerivCLM ℝ (coordinateVector i) phi

theorem coordinateTestDerivative_apply (i : Fin 3) (phi : 𝓓(ballOpens, ℝ)) (x : R3) :
    coordinateTestDerivative i phi x = fderiv ℝ (phi : R3 → ℝ) x (coordinateVector i) := by
  change (TestFunction.lineDerivCLM ℝ (coordinateVector i) phi : 𝓓(ballOpens, ℝ)) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le le_top,
    (phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]

theorem coordinateTestDerivative_commute (i j : Fin 3) (phi : 𝓓(ballOpens, ℝ)) :
    coordinateTestDerivative i (coordinateTestDerivative j phi) =
      coordinateTestDerivative j (coordinateTestDerivative i phi) := by
  have hfun (l : Fin 3) : (coordinateTestDerivative l phi : R3 → ℝ) =
      (smoothCoordinateDerivative (⟨phi,phi.contDiff⟩ : SmoothData) l).1 := by
    funext x
    exact coordinateTestDerivative_apply l phi x
  ext x
  rw [coordinateTestDerivative_apply,coordinateTestDerivative_apply,hfun j,hfun i]
  exact congrArg (fun f : SmoothData => f.1 x)
    (smoothCoordinateDerivative_commute (⟨phi,phi.contDiff⟩ : SmoothData) i j)

theorem value_coordinateTestDerivative_eq_gradient (i : Fin 3) (phi : 𝓓(ballOpens, ℝ)) :
    TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2
      (coordinateTestDerivative i phi)) =
    unitBallCoordinateGradientL i (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 phi) := by
  rw [TauCeti.W1p.value_ofTestFunctionₗ]
  apply Lp.ext
  filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
      (coordinateTestDerivative i phi),unitBallCoordinateGradientL_testFunction_ae i phi]
    with x hv hg
  rw [hv,hg,coordinateTestDerivative_apply,
    (phi.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily
