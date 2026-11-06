import Calderon.ActualReferenceRotationStrongZeroAngle

/-! Expanded first in EXPANSION-actual-rotation-strong-zero-room-lift-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


def referenceRotationStrongInvertibleLocus (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    Set (ℝ × (ℝ × (R3 × ℝ))) :=
  {t | (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible}

lemma isOpen_referenceRotationStrongInvertibleLocus (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    IsOpen (referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (contDiff_referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).continuous

lemma referenceRotationStrongInvertibleLocus_zero_angle
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    (0,p) ∈ referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j := by
  change (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (0,p)).IsInvertible
  rw [referenceRotationStrongDirichletFamily_zero_angle]
  exact hi

lemma eventually_referenceRotationStrongDirichletFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ∀ᶠ t in 𝓝 ((0 : ℝ),p),
      (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible :=
  (isOpen_referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j).mem_nhds
    (referenceRotationStrongInvertibleLocus_zero_angle g L y0 Φ B ε C ρ H a w hData hcalc i j p hi)

lemma exists_ball_referenceRotationStrongInvertibleLocus
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ∃ η : ℝ, 0 < η ∧ ball ((0 : ℝ),p) η ⊆
      referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j :=
  Metric.isOpen_iff.mp
    (isOpen_referenceRotationStrongInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc i j) (0,p)
    (referenceRotationStrongInvertibleLocus_zero_angle g L y0 Φ B ε C ρ H a w hData hcalc i j p hi)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationStrongInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceRotationStrongInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationStrongInvertibleLocus_zero_angle
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceRotationStrongDirichletFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_ball_referenceRotationStrongInvertibleLocus
