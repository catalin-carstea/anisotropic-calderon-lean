import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy

/-! Exact diagnostic partition of immutable weak-energy efd9; declaration blocks/context unchanged. Parent checking pending. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
def nativeFiniteForcingValueL (J : BallH1Zero →L[ℝ] BallH1)
    (Q : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] StrongDual ℝ BallH1Zero :=
  forcingFromValueL (Q.comp J)

theorem nativeFiniteForcingValueL_eq (J : BallH1Zero →L[ℝ] BallH1)
    (Q : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    nativeFiniteForcingValueL J Q = forcingFromValueL (Q.comp J) := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
