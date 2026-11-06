import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing

/-! Exact diagnostic partition of immutable weak-energy efd9; declaration blocks/context unchanged. Parent checking pending. -/
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

theorem jointReferenceWeightedDrift_data :
    ContDiff ℝ ∞ (conformalReferenceWeightedFramedDrift g L Φ H w) ∧
    ∀ p z, z ∉ closedBall (0 : R3) 3 →
      conformalReferenceWeightedFramedDrift g L Φ H w (p,z) = 0 := by
  refine ⟨hData.2.2.2.1,?_⟩
  intro p z hz
  have hz3 : 3 ≤ ‖z‖ := le_of_lt (by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
  exact hData.2.2.2.2.2.2.1 (p,z) hz3

def referenceWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let F : SmoothCoefficientMatrix 1 := commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1 p
  let G : Fin 3 → SmoothCoefficientJets 1 := fun i =>
    commonSupportCoefficientFamily 1
      (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
      ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
      (fun t z hz => by rw [hc.2 t z hz]; rfl) p
  let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
  let J : BallH1Zero →L[ℝ] BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
  let V : BallH1 →L[ℝ] E0 :=
    TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  let M : Fin 3 → Fin 3 → E0 →L[ℝ] E0 := fun i j => coefficientMultiplier hcalc 0 (F i j)
  let Mc : Fin 3 → E0 →L[ℝ] E0 := fun i => coefficientMultiplier hcalc 0 (G i)
  let P : Fin 3 → E0 →L[ℝ] StrongDual ℝ BallH1Zero :=
    fun i => forcingFromValueL ((D i).comp J)
  let P0 : E0 →L[ℝ] StrongDual ℝ BallH1Zero := forcingFromValueL (V.comp J)
  (∑ i : Fin 3, ∑ j : Fin 3, (P i).comp ((M i j).comp (D j))) +
    ∑ i : Fin 3, P0.comp ((Mc i).comp (D i))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
