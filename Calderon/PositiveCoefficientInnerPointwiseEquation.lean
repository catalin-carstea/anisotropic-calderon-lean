import Calderon.LocalSmoothFluxDivergence
import Calderon.ConformalFluxDivergence

/-! The classical flux equation is derived for the literal positive-coefficient native solver. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace Matrix
open scoped ENNReal ContDiff InnerProductSpace Topology Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem exists_positiveCoefficientDirichletSolution_pointwise_equation_innerBall
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) a) ∧
      ((TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F) ∧
      ∀ x ∈ ball (0 : R3) a,
        ConnectionError.coordinateFluxDivergence
          (fun y => MetricOperator.matrixOperatorMap (A y) (gradient F y : R3)) x = 0 := by
  classical
  obtain ⟨F,hF,hSmooth,hValue,hWeak⟩ :=
    exists_positiveCoefficientDirichletSolution_classical_weakEquation_innerBall
      hcalc hreg τ0 A hA hPos f a ha ha1
  let Ω : Opens R3 := ⟨ball (0 : R3) a,isOpen_ball⟩
  let Z : R3 → R3 := fun x => MetricOperator.matrixOperatorMap (A x) (gradient F x : R3)
  let Fi : Fin 3 → R3 → ℝ := fun i x => Z x i
  have hDerivative : ContDiffOn ℝ ∞ (fderiv ℝ F) (ball (0 : R3) a) :=
    hSmooth.fderiv_of_isOpen isOpen_ball (by simp)
  have hGradientCoordinate (j : Fin 3) :
      ContDiffOn ℝ ∞ (fun x => (gradient F x : R3) j) (ball (0 : R3) a) := by
    have hDirectional : ContDiffOn ℝ ∞
        (fun x => fderiv ℝ F x (MetricVolume.coordinateVector j)) (ball (0 : R3) a) :=
      hDerivative.clm_apply contDiffOn_const
    exact hDirectional.congr (fun x _ => by
      simpa only [gradient] using MetricVolume.riesz_coordinate (fderiv ℝ F x) j)
  have hRows (i : Fin 3) : ContDiffOn ℝ ∞ (Fi i) Ω := by
    have hSum : ContDiffOn ℝ ∞
        (fun x => ∑ j : Fin 3, A x i j * (gradient F x : R3) j) (ball (0 : R3) a) :=
      ContDiffOn.sum (fun j _ =>
        (contDiff_pi.mp (contDiff_pi.mp hA i) j).contDiffOn.mul (hGradientCoordinate j))
    exact hSum.congr (fun x _ => by
      dsimp only [Fi,Z]
      exact MetricVolume.matrixOperator_coordinate (A x) (gradient F x : R3) i)
  have hRowsWeak : ∀ φ : SmoothData, HasCompactSupport φ.1 → tsupport φ.1 ⊆ (Ω : Set R3) →
      ∫ x : R3, (∑ i : Fin 3,
        lineDeriv ℝ φ.1 x (MetricVolume.coordinateVector i) * Fi i x)
        ∂(volume : Measure R3) = 0 := by
    intro φ hCompact hSupport
    have hDensity (x : R3) :
        (∑ i : Fin 3, lineDeriv ℝ φ.1 x (MetricVolume.coordinateVector i) * Fi i x) =
          (gradient φ.1 x : R3) ⬝ᵥ (A x *ᵥ (gradient F x : R3)) := by
      simp only [lineDeriv_smoothData_coordinate_eq_gradient,Fi,Z,
        MetricVolume.matrixOperator_coordinate,Matrix.mulVec,dotProduct]
    have hIntegral :
        (∫ x : R3, (∑ i : Fin 3,
          lineDeriv ℝ φ.1 x (MetricVolume.coordinateVector i) * Fi i x)
          ∂(volume : Measure R3)) =
        ∫ x : R3, (gradient φ.1 x : R3) ⬝ᵥ (A x *ᵥ (gradient F x : R3))
          ∂(volume : Measure R3) := integral_congr_ae (Filter.Eventually.of_forall hDensity)
    exact hIntegral.trans (hWeak φ hCompact hSupport)
  have hDiv := coordinateFluxRows_divergence_zero_of_smooth_weakEquation Ω Fi hRows hRowsWeak
  refine ⟨F,hF,hSmooth,hValue,?_⟩
  intro x hx
  simpa only [ConnectionError.coordinateFluxDivergence,Fi,Z,
    NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector] using hDiv x hx

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_positiveCoefficientDirichletSolution_pointwise_equation_innerBall
