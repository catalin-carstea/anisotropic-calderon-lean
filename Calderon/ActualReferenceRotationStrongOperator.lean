import Calderon.ActualReferenceRotationMultiplierTopology
import Calderon.OrdinaryWeightedDriftOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
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

/-! The drift multiplier already contains the full weighted drift coefficient. -/

def referenceRotationOrdinaryStrongFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ordinaryPrincipalL hcalc 0
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) +
  ∑ l : Fin 3, (referenceRotationDriftMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 i j l t).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 l)

lemma contDiff_referenceRotationOrdinaryStrongFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationOrdinaryStrongFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) := by
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    exact contDiff_referenceRotationPrincipalMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 i j k l
  have hP : ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
      (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm
  apply hP.add
  apply ContDiff.sum
  intro l hl
  exact (contDiff_referenceRotationDriftMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 i j l).clm_comp contDiff_const

def referenceRotationStrongDirichletFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
    (strongDirichletSubmodule 0).toSubmodule.subtypeL

lemma referenceRotationStrongDirichletFamily_restriction (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).comp
        (strongDirichletSubmodule 0).toSubmodule.subtypeL := rfl

lemma contDiff_referenceRotationStrongDirichletFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j) :=
  (contDiff_referenceRotationOrdinaryStrongFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j).clm_comp contDiff_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOrdinaryStrongFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationOrdinaryStrongFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationStrongDirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationStrongDirichletFamily_restriction

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationStrongDirichletFamily
