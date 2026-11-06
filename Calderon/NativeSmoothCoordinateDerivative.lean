import Calderon.NativeSmoothBallSobolev
import Calderon.SobolevDivergenceAssembly
import Calderon.MetricHessianDivergence

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

/-- The genuine ambient coordinate derivative, with smoothness proved from the datum. -/
def smoothCoordinateDerivative (f : SmoothData) (i : Fin 3) : SmoothData :=
  ⟨fun x => fderiv ℝ f.1 x (coordinateVector i), (f.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩

theorem unitBallCoordinateDerivativeL_smoothBallSobolev_value_ae
    (hcalc : FixedSobolevCalculus) (k : ℕ) (i : Fin 3) (f : SmoothData) :
    TauCeti.Wkp.value k
      (unitBallCoordinateDerivativeL hcalc k i (smoothBallSobolev (k + 1) f))
      =ᵐ[(volume : Measure R3).restrict ballOpens] (smoothCoordinateDerivative f i).1
      := by
  have hder := unitBallCoordinateDerivativeL_value_ae hcalc k i
    (smoothBallSobolev (k + 1) f)
  rw [firstOrder_smoothBallSobolev] at hder
  filter_upwards [hder, gradient_smoothSobolev_ae f] with x hx hy
  rw [hx, hy]
  exact gradient_coordinate f.1 x i

/-- Compatibility with the published ordinary calculus on the actual graph spaces. -/
theorem unitBallCoordinateDerivativeL_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (k : ℕ) (i : Fin 3) (f : SmoothData) :
    unitBallCoordinateDerivativeL hcalc k i (smoothBallSobolev (k + 1) f) =
      smoothBallSobolev k (smoothCoordinateDerivative f i) := by
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  exact (unitBallCoordinateDerivativeL_smoothBallSobolev_value_ae hcalc k i f).trans
    (value_smoothBallSobolev_ae k (smoothCoordinateDerivative f i)).symm

end OAI.AnisotropicCalderon.DirichletFamily
