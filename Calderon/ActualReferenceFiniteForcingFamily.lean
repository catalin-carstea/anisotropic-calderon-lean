import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy
import Calderon.NativeFiniteForcingEnergyTopology
import Calderon.ActualReferenceWeakEnergyDecomposition
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

def referenceFiniteForcingEnergyFamily (hcalc : FixedSobolevCalculus) :
    (ℝ × (R3 × ℝ)) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
      let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
      let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
      let K : Set R3 := closedBall (0 : R3) 3
      let hK : IsCompact K := isCompact_closedBall _ _
      let J : BallH1Zero →L[ℝ] BallH1 :=
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
      let F : (ℝ × (R3 × ℝ)) → SmoothCoefficientMatrix 1 :=
        commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1
      let G : Fin 3 → (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 1 := fun i =>
        commonSupportCoefficientFamily 1
          (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
          ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
          (fun t z hz => by rw [hc.2 t z hz]; rfl)
      let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
      let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
      let V : BallH1 →L[ℝ] E0 :=
        TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      let M : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → E0 →L[ℝ] E0 :=
        fun i j p => coefficientMultiplier hcalc 0 (F p i j)
      let Mc : Fin 3 → (ℝ × (R3 × ℝ)) → E0 →L[ℝ] E0 :=
        fun i p => coefficientMultiplier hcalc 0 (G i p)
      let P : Fin 3 → E0 →L[ℝ] StrongDual ℝ BallH1Zero :=
        fun i => forcingFromValueL ((D i).comp J)
      let P0 : E0 →L[ℝ] StrongDual ℝ BallH1Zero := forcingFromValueL (V.comp J)
      fun p : ℝ × (R3 × ℝ) =>
        (∑ i : Fin 3, ∑ j : Fin 3, (P i).comp ((M i j p).comp (D j))) +
          ∑ i : Fin 3, P0.comp ((Mc i p).comp (D i))


theorem referenceWeakEnergyFamily_eq_referenceFiniteForcingEnergyFamily
    (hcalc : FixedSobolevCalculus) :
    referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc =
      referenceFiniteForcingEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc := by
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
