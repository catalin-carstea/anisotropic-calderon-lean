import Calderon.ActualReferenceRotationStrongOperator
import Calderon.NativeStrongCoefficientCongruence
import Calderon.ActualReferenceStrongRoom
import Calderon.CoordinateRotationCoefficientFamily

/-! Expanded first in EXPANSION-actual-rotation-strong-zero-room-lift-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationOrdinaryStrongFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p) =
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData p.1
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2
    (jointFixedParameterSlice a p.1) h.1 (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p.2
  have hfield : coefficientMatrixField 2
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (0,p)) =
      coefficientMatrixField 2 F := by
    rw [coefficientMatrixField_referenceRotationPrincipalJetsFamily]
    change (fun x => coordinateRotationPrincipalFamily i j a ((0,p),x)) =
      coefficientMatrixField 2 (commonSupportMatrixFamily 2
        (jointFixedParameterSlice a p.1) h.1 (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p.2)
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact funext (coordinateRotationPrincipalFamily_zero_angle i j a p)
  have hP := ordinaryPrincipalL_eq_of_coefficientMatrixField_eq hcalc 0 _ F hfield
  have hG (l : Fin 3) (x : R3) :
      coefficientValue 1 (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l (0,p)) x =
        weightedDriftSlice (jointFixedParameterSlice w p.1)
          (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) p.1) L p.2 x l := by
    rw [coefficientValue_referenceRotationDriftJetsFamily,coordinateRotationDriftFamily_zero_angle,
      weightedDriftSlice_reference_eq g L y0 Φ B ε C ρ H a w hData p.1 p.2]
  have hDrift := sum_fullWeightedDriftMultipliers_eq_ordinaryWeightedDriftL hcalc 0
    (jointFixedParameterSlice w p.1) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) p.1) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.2 L p.2
    (fun l => referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l (0,p)) hG
  exact congrArg₂ (fun X Y : BallSobolev 2 →L[ℝ] BallSobolev 0 => X+Y) hP hDrift

lemma referenceRotationStrongDirichletFamily_zero_angle
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p) =
      referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 :=
  congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 0 =>
    T.comp (strongDirichletSubmodule 0).toSubmodule.subtypeL)
    (referenceRotationOrdinaryStrongFamily_zero_angle g L y0 Φ B ε C ρ H a w hData hcalc i j p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOrdinaryStrongFamily_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationStrongDirichletFamily_zero_angle
