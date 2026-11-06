import Calderon.ActualReferenceTwoAngleStrongOperator
import Calderon.ActualReferenceTwoAngleAdjointMassFamily
import Calderon.NativeSupportedAdjointStrongForcing
/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-strong-v036.md. -/
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
include hData

lemma contDiff_referenceTwoAnglePrincipalOperatorFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) := by
    apply contDiff_pi.mpr
    intro d
    apply contDiff_pi.mpr
    intro e
    exact contDiff_referenceTwoAnglePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 i j k l d e
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

lemma contDiff_referenceTwoAngleTransposePrincipalOperatorFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))) := by
    apply contDiff_pi.mpr
    intro d
    apply contDiff_pi.mpr
    intro e
    exact contDiff_referenceTwoAnglePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 i j k l e d
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

def referenceTwoAngleAdjointMassForcingFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  (nativeCoefficientMassL hcalc
    (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)).comp nativeH2FirstOrderL

lemma contDiff_referenceTwoAngleAdjointMassForcingFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (referenceTwoAngleAdjointMassFunction g L Φ H w i j k l)
    (contDiff_referenceTwoAngleAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j k l)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j k l)
  exact (hm.clm_comp contDiff_const).clm_comp contDiff_const

def referenceTwoAngleAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) +
    (ordinaryPrincipalL hcalc 0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) -
      referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t) +
    referenceTwoAngleAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t

lemma contDiff_referenceTwoAngleAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l) :=
  ((contDiff_referenceTwoAngleTransposePrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).add
    ((contDiff_referenceTwoAnglePrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).sub
      (contDiff_referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l))).add
        (contDiff_referenceTwoAngleAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAnglePrincipalOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleTransposePrincipalOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMassForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointMassForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointOrdinaryStrongFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointOrdinaryStrongFamily
