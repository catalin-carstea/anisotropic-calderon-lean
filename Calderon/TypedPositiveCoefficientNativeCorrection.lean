import Calderon.TypedPositiveCoefficientFormCoercivity
import Calderon.TypedCoefficientNativeInverseConstructor
import Calderon.NativeCoerciveFunctionalInverseUniqueness
import Calderon.PositiveCoefficientAffineAllOrderRegularity
import Calderon.NativeCoefficientWeakEnergy

/-! EXPANSION.json precedes the same-energy typed inverse construction.
The prior raw constructor remains preserved openly. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def coefficientFormDirichletCorrection
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef)
    (f : SmoothData) : BallH1Zero :=
  let hcoeff := memLp_continuousCoefficientEnergyIntegrand A hA.continuous
  unitBallCoefficientNativeInverse
    (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)))
    (-(nativeCoefficientWeakEnergyL A (0 : R3 → R3) (0 : R3 → ℝ) hcoeff (smoothSobolev f)))

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse

theorem coefficientFormDirichletCorrection_eq_native
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    coefficientFormDirichletCorrection A hA hPos f =
      positiveCoefficientDirichletCorrection A hA hPos f := by
  let hcoeff := memLp_continuousCoefficientEnergyIntegrand A hA.continuous
  let B : BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := unitBallCoefficientEnergyL
    (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)))
  let ell : StrongDual ℝ BallH1Zero :=
    -(nativeCoefficientWeakEnergyL A (0 : R3 → R3) (0 : R3 → ℝ) hcoeff (smoothSobolev f))
  have hB : IsCoercive B := isCoercive_unitBallCoefficientEnergyL_positiveCoefficient
    A hA.continuous hPos hcoeff
  let z : BallH1Zero := positiveCoefficientDirichletCorrection A hA hPos f
  have hU : positiveCoefficientDirichletSolution A hA hPos f = smoothSobolev f + (z : BallH1) := rfl
  change nativeZeroFunctionalInverse B ell = z
  symm
  apply eq_nativeZeroFunctionalInverse_of_coercive B hB ell z
  intro v
  have hWeak : TauCeti.PDE.energyFormH1 A 0 0
      (positiveCoefficientDirichletSolution A hA hPos f) (v : BallH1) = 0 :=
    positiveCoefficientDirichletSolution_weakEquation A hA hPos f v
  have hb : (fun x : R3 => (0 : R3)) = (0 : R3 → R3) := rfl
  have hc : (fun x : R3 => (0 : ℝ)) = (0 : R3 → ℝ) := rfl
  have hAdd0 : TauCeti.PDE.energyFormH1 A
      (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ))
      (smoothSobolev f + (z : BallH1)) (v : BallH1) =
      TauCeti.PDE.energyFormH1 A (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ))
        (smoothSobolev f) (v : BallH1) +
      TauCeti.PDE.energyFormH1 A (fun x : R3 => (0 : R3)) (fun x : R3 => (0 : ℝ))
        (z : BallH1) (v : BallH1) :=
    TauCeti.PDE.energyFormH1_add_left (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := A) (b := fun x : R3 => (0 : R3)) (c := fun x : R3 => (0 : ℝ))
      (u := smoothSobolev f) (v := (v : BallH1)) (w := (z : BallH1)) hcoeff
  have hAdd : TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ)
      (smoothSobolev f + (z : BallH1)) (v : BallH1) =
      TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (smoothSobolev f) (v : BallH1) +
      TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (z : BallH1) (v : BallH1) := by
    simpa only [hb,hc] using hAdd0
  have hTest := congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
    A (0 : R3 → R3) (0 : R3 → ℝ) u (v : BallH1)) hU
  have hSum : TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ)
      (smoothSobolev f) (v : BallH1) +
      TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (z : BallH1) (v : BallH1) = 0 :=
    hAdd.symm.trans (hTest.symm.trans hWeak)
  have hNative : TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ)
      (z : BallH1) (v : BallH1) =
      -TauCeti.PDE.energyFormH1 A (0 : R3 → R3) (0 : R3 → ℝ) (smoothSobolev f) (v : BallH1) := by
    linarith
  have hForcing : ell v = -TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      A (0 : R3 → R3) (0 : R3 → ℝ) (smoothSobolev f) (v : BallH1) := by
    dsimp only [ell]
    rw [ContinuousLinearMap.neg_apply,nativeCoefficientWeakEnergyL_apply]
  exact (unitBallCoefficientEnergyL_apply_eq_energyFormH1 A hcoeff z v).trans
    (hNative.trans hForcing.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientFormDirichletCorrection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientFormDirichletCorrection_eq_native
