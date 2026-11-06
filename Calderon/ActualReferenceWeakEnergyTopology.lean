import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy
import Calderon.NativeFiniteForcingEnergyTopology
import Calderon.ActualReferenceWeakEnergyDecomposition
import Calderon.ActualReferenceFiniteForcingFamily
import Calderon.ActualReferenceFiniteForcingTopology
import Calderon.InheritedNormedStructureData
import Calderon.LpInheritedStructureData
import Calderon.ClmInheritedStructureData

/-! Exact diagnostic partition of immutable weak-energy efd9; declaration blocks/context unchanged. Parent checking pending. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
private abbrev nativeStrongDualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual ℝ BallH1Zero) :=
  NormedAddCommGroup.ofSeparation (fun (f : StrongDual ℝ BallH1Zero) (hf : ‖f‖ = 0) => by
    apply ContinuousLinearMap.ext
    intro v
    change f v = 0
    apply norm_le_zero_iff.mp
    calc
      ‖f v‖ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
      _ = 0 := by rw [hf, zero_mul])

attribute [local instance] nativeStrongDualNormedAddCommGroup

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem contDiff_referenceWeakEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  have hFamily := referenceWeakEnergyFamily_eq_referenceFiniteForcingEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc
  have hEq := congrArg (ContDiff ℝ ∞) hFamily
  have hT := contDiff_referenceFiniteForcingEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc
  exact Eq.mpr hEq hT

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
