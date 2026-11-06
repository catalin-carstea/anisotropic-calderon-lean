import Calderon.ActualReferenceTwoAngleMultipliers
import Calderon.OrdinaryWeightedDriftOperator

/-! Genuine native strong operator of nested rotated actual coefficients, and its
literal inverse room. -/
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

def referenceTwoAngleOrdinaryStrongFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ordinaryPrincipalL hcalc 0
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) +
  ∑ d : Fin 3, (referenceTwoAngleDriftMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d t).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 d)

def referenceTwoAngleStrongDirichletFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 :=
  (referenceTwoAngleOrdinaryStrongFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp
      (strongDirichletSubmodule 0).toSubmodule.subtypeL

lemma contDiff_referenceTwoAngleOrdinaryStrongFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleOrdinaryStrongFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) := by
    apply contDiff_pi.mpr
    intro d
    apply contDiff_pi.mpr
    intro e
    exact contDiff_referenceTwoAnglePrincipalMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 i j k l d e
  have hp : ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
      (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm
  apply hp.add
  apply ContDiff.sum
  intro d hd
  exact (contDiff_referenceTwoAngleDriftMultiplierFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 i j k l d).clm_comp contDiff_const

lemma contDiff_referenceTwoAngleStrongDirichletFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l) :=
  (contDiff_referenceTwoAngleOrdinaryStrongFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l).clm_comp contDiff_const

lemma isOpen_referenceTwoAngleStrong_inverse_set (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    IsOpen {t : ℝ × (ℝ × (ℝ × (R3 × ℝ))) |
      (referenceTwoAngleStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible} := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (contDiff_referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l).continuous

lemma contDiffAt_referenceTwoAngleStrong_inverse (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hInv : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l z).inverse) t := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  exact hInv.contDiffAt_map_inverse.comp t
    (contDiff_referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l).contDiffAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryStrongFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleOrdinaryStrongFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleStrongDirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceTwoAngleStrong_inverse_set
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleStrong_inverse
