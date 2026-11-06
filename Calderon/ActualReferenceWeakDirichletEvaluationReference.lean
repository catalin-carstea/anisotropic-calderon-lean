import Calderon.ActualReferenceWeakDirichletConstruction
import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.ActualReferenceWeakEnergyApply

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem referenceWeakDirichletEnergyFamily_apply_reference (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u v : BallH1Zero) :
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v =
      referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (u : BallH1) v := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
