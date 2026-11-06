import Calderon.ActualReferenceTwoAngleStrongOperator
import Calderon.ActualReferenceRotationStrongZeroAngle
import Calderon.NativeStrongCoefficientCongruence

/-! The zero-angle identity and local strong inverse membership, from the
original inverse. -/
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

open Filter
open scoped Topology

lemma referenceTwoAngleOrdinaryStrongFamily_zero_outer_angle
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ)) :
    referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(φ,p)) =
      referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) := by
  have hField : coefficientMatrixField 2
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l (0,(φ,p))) =
    coefficientMatrixField 2
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 k l (φ,p)) := by
    rw [coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily,
      coefficientMatrixField_referenceRotationPrincipalJetsFamily]
    exact funext (coordinateRotationPrincipalFamily_zero_angle i j
      (coordinateRotationPrincipalFamily k l a) (φ,p))
  have hP := ordinaryPrincipalL_eq_of_coefficientMatrixField_eq hcalc 0 _ _ hField
  have hDrift (d : Fin 3) : referenceTwoAngleDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d (0,(φ,p)) =
    referenceRotationDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 k l d (φ,p) := by
    have h := coefficientMultiplier_eq_smul_of_value_eq hcalc 0
      (referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l d (0,(φ,p)))
      (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 k l d (φ,p)) 1 (by
        intro x
        rw [coefficientValue_referenceTwoAngleDriftJetsFamily,
          coefficientValue_referenceRotationDriftJetsFamily,one_mul]
        exact congrArg (fun v : R3 => v d) (coordinateRotationDriftFamily_zero_angle i j
          (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w)) (φ,p) x))
    simpa only [referenceTwoAngleDriftMultiplierFamily,referenceRotationDriftMultiplierFamily,one_smul] using h
  have hSum : (∑ d : Fin 3, (referenceTwoAngleDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d (0,(φ,p))).comp
        (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 d)) =
    ∑ d : Fin 3, (referenceRotationDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 k l d (φ,p)).comp
        (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 d) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact congrArg (fun T : BallSobolev 0 →L[ℝ] BallSobolev 0 =>
      T.comp (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 d)) (hDrift d)
  exact congrArg₂ (fun X Y : BallSobolev 2 →L[ℝ] BallSobolev 0 => X+Y) hP hSum

lemma referenceTwoAngleStrongDirichletFamily_zero_outer_angle
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (φ : ℝ) (p : ℝ × (R3 × ℝ)) :
    referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(φ,p)) =
      referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc k l (φ,p) :=
  congrArg (fun T : BallSobolev 2 →L[ℝ] BallSobolev 0 =>
    T.comp (strongDirichletSubmodule 0).toSubmodule.subtypeL)
    (referenceTwoAngleOrdinaryStrongFamily_zero_outer_angle
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l φ p)

lemma referenceTwoAngleStrongDirichletFamily_zero_angles
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (p : ℝ × (R3 × ℝ)) :
    referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(0,p)) =
      referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 :=
  (referenceTwoAngleStrongDirichletFamily_zero_outer_angle
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l 0 p).trans
      (referenceRotationStrongDirichletFamily_zero_angle
        g L y0 Φ B ε C ρ H a w hData hcalc k l p)

lemma eventually_referenceTwoAngleStrong_inverse_of_original
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ∀ᶠ t in 𝓝 ((0 : ℝ),((0 : ℝ),p)),
      (referenceTwoAngleStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible := by
  have hZero : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(0,p))).IsInvertible := by
    rw [referenceTwoAngleStrongDirichletFamily_zero_angles]
    exact hi
  exact (isOpen_referenceTwoAngleStrong_inverse_set
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l).mem_nhds hZero

lemma exists_ball_referenceTwoAngleStrong_inverse_of_original
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ∃ η : ℝ, 0 < η ∧ ball ((0 : ℝ),((0 : ℝ),p)) η ⊆
      {t | (referenceTwoAngleStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible} := by
  have hZero : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l (0,(0,p))).IsInvertible := by
    rw [referenceTwoAngleStrongDirichletFamily_zero_angles]
    exact hi
  exact Metric.isOpen_iff.mp (isOpen_referenceTwoAngleStrong_inverse_set
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l) (0,(0,p)) hZero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryStrongFamily_zero_outer_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleStrongDirichletFamily_zero_outer_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleStrongDirichletFamily_zero_angles
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceTwoAngleStrong_inverse_of_original
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_ball_referenceTwoAngleStrong_inverse_of_original
