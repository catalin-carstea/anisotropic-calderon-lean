import Calderon.PositiveCoefficientAffineAllOrderRegularity
import Calderon.NativeInteriorDirectSmoothReconstruction
import Calderon.LocalSmoothAmbientExtension

/-! Full upfront: EXPANSION.json.
Actual positive coefficient weak solver, derived all-order regularity and interior smooth realization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem exists_contDiffOn_positiveCoefficientDirichletSolution_innerBall
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) a) ∧
      (TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F := by
  obtain ⟨U,hU,hCoherence⟩ :=
    exists_coherent_positiveCoefficientDirichletSolution_allOrderLifts hcalc hreg τ0 A hA hPos f
  have hValue (n : ℕ) : TauCeti.Wkp.value (n+2) (U n) =
      TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) := by
    simpa only [TauCeti.Wkp.value_firstOrder] using
      congrArg (fun u : BallH1 => TauCeti.W1p.value u) (hU n)
  have hSame (n : ℕ) : TauCeti.Wkp.value (n+2) (U n) = TauCeti.Wkp.value 2 (U 0) :=
    (hValue n).trans (hValue 0).symm
  obtain ⟨F,hF,hSmooth,hRep⟩ :=
    exists_contDiffOn_infty_of_nativeAllOrderValues hcalc U hSame a ha ha1
  refine ⟨F,hF,hSmooth,?_⟩
  filter_upwards [hRep] with x hx
  exact (congrArg (fun p : BallSobolev 0 => (p : R3 → ℝ) x) (hValue 0)).symm.trans hx

theorem exists_smoothData_positiveCoefficientDirichletSolution_eq_on_innerClosedBall
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ φ : SmoothData, HasCompactSupport φ.1 ∧
      ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
        x ∈ closedBall (0 : R3) a →
          φ.1 x = TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) x := by
  let b : ℝ := (a+1)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb : 0 < b := ha.trans hab
  have hb1 : b < 1 := by dsimp [b]; linarith
  obtain ⟨F,hF,hSmooth,hRep⟩ :=
    exists_contDiffOn_positiveCoefficientDirichletSolution_innerBall hcalc hreg τ0 A hA hPos f b hb hb1
  obtain ⟨φ,hCompact,hNear⟩ := exists_smoothData_eq_near_compact
    (closedBall (0 : R3) a) (ball (0 : R3) b)
    (isCompact_closedBall (0 : R3) a) isOpen_ball (closedBall_subset_ball hab) F hSmooth
  have hGlobal : ∀ᵐ x ∂(volume : Measure R3), x ∈ ball (0 : R3) b →
      TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) x = F x :=
    (ae_restrict_iff' isOpen_ball.measurableSet).mp hRep
  refine ⟨φ,hCompact,?_⟩
  filter_upwards [ae_restrict_of_ae hGlobal] with x hx
  intro hxA
  exact ((hNear x hxA).eq_of_nhds).trans (hx (closedBall_subset_ball hab hxA)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_contDiffOn_positiveCoefficientDirichletSolution_innerBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_smoothData_positiveCoefficientDirichletSolution_eq_on_innerClosedBall
