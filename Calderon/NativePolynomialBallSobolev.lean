import Calderon.NativeSmoothCoordinateDerivative
import Calderon.GreenRadialTrace

noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge MetricVolume

/-- The actual coordinate map from Euclidean `R3` to the finite product used by polynomial eval. -/
def polynomialCoordinateMap : R3 →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i => (EuclideanSpace.proj i : R3 →L[ℝ] ℝ))

theorem polynomialCoordinateMap_apply (x : R3) :
    polynomialCoordinateMap x = (fun i => x i) := rfl

theorem contDiff_polynomialEval (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (fun x : R3 => eval (polynomialCoordinateMap x) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa only [eval_C] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => c))
  | add p q hp hq =>
      simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      convert! hp.mul (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff using 1
      ext x
      simp only [map_mul, eval_X, polynomialCoordinateMap_apply,
        EuclideanSpace.coe_proj]

def smoothPolynomialData (p : MvPolynomial (Fin 3) ℝ) : SmoothData :=
  ⟨fun x => eval (polynomialCoordinateMap x) p, contDiff_polynomialEval p⟩

theorem hasFDerivAt_polynomialEval (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    HasFDerivAt (fun y : R3 => eval (polynomialCoordinateMap y) p)
      ((GreenRadialTrace.polynomialFDeriv p (polynomialCoordinateMap x)).comp
        polynomialCoordinateMap) x := by
  exact (GreenRadialTrace.hasFDerivAt_eval p (polynomialCoordinateMap x)).comp x
    polynomialCoordinateMap.hasFDerivAt

theorem fderiv_polynomialEval_apply (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y) p) x v =
      ∑ i : Fin 3, v i * eval (fun j => x j) (pderiv i p) := by
  rw [(hasFDerivAt_polynomialEval p x).fderiv, ContinuousLinearMap.comp_apply,
    GreenRadialTrace.polynomialFDeriv_apply]
  simp only [polynomialCoordinateMap_apply]

theorem fderiv_polynomialEval_coordinate (p : MvPolynomial (Fin 3) ℝ)
    (x : R3) (i : Fin 3) :
    fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y) p) x (coordinateVector i) =
      eval (fun j => x j) (pderiv i p) := by
  simp [fderiv_polynomialEval_apply, coordinateVector, PiLp.single_apply, ite_mul]

theorem smoothCoordinateDerivative_smoothPolynomialData
    (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    smoothCoordinateDerivative (smoothPolynomialData p) i =
      smoothPolynomialData (pderiv i p) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y : R3 => eval (polynomialCoordinateMap y) p)
    x (coordinateVector i) = eval (polynomialCoordinateMap x) (pderiv i p)
  rw [fderiv_polynomialEval_coordinate, polynomialCoordinateMap_apply]

def polynomialBallSobolev (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) : BallSobolev k :=
  smoothBallSobolev k (smoothPolynomialData p)

theorem value_polynomialBallSobolev_ae (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.value k (polynomialBallSobolev k p)
      =ᵐ[(volume : Measure R3).restrict ballOpens] (fun x => eval (fun i => x i) p)
      := by
  simpa only [polynomialBallSobolev, smoothPolynomialData, polynomialCoordinateMap_apply]
    using value_smoothBallSobolev_ae k (smoothPolynomialData p)

theorem firstOrder_polynomialBallSobolev (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.firstOrder k (polynomialBallSobolev (k + 1) p) =
      smoothSobolev (smoothPolynomialData p) := by
  exact firstOrder_smoothBallSobolev k (smoothPolynomialData p)

theorem unitBallCoordinateDerivativeL_polynomialBallSobolev
    (hcalc : FixedSobolevCalculus) (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    unitBallCoordinateDerivativeL hcalc k i (polynomialBallSobolev (k + 1) p) =
      polynomialBallSobolev k (pderiv i p) := by
  change unitBallCoordinateDerivativeL hcalc k i
    (smoothBallSobolev (k + 1) (smoothPolynomialData p)) =
      smoothBallSobolev k (smoothPolynomialData (pderiv i p))
  rw [unitBallCoordinateDerivativeL_smoothBallSobolev,
    smoothCoordinateDerivative_smoothPolynomialData]

end OAI.AnisotropicCalderon.DirichletFamily
