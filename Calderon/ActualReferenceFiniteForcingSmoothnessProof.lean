import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy
import Calderon.NativeFiniteForcingEnergyTopology
import Calderon.ActualReferenceWeakEnergyDecomposition
import Calderon.ActualReferenceFiniteForcingFamily
import Calderon.ActualReferencePrincipalMultiplierTopology
import Calderon.ActualReferenceDriftMultiplierTopology
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

def referenceFiniteForcingEnergySmoothnessProof (hcalc : FixedSobolevCalculus) :=
  let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
  let J : BallH1Zero →L[ℝ] BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
  let V : BallH1 →L[ℝ] E0 :=
    TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  let M : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → E0 →L[ℝ] E0 :=
    referencePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc
  let Mc : Fin 3 → (ℝ × (R3 × ℝ)) → E0 →L[ℝ] E0 :=
    referenceDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc
  let hM := contDiff_referencePrincipalMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc
  let hMc := contDiff_referenceDriftMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc
  contDiff_nativeFiniteForcingEnergy J D V M Mc hM hMc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
