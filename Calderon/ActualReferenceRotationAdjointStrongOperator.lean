import Calderon.ActualReferenceRotationStrongOperator
import Calderon.ActualReferenceRotationAdjointMassFamily
import Calderon.NativeSupportedAdjointStrongForcing
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
include hData

lemma contDiff_referenceRotationPrincipalOperatorFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) := by
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    exact contDiff_referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 i j k l
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

lemma contDiff_referenceRotationTransposePrincipalOperatorFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => ordinaryPrincipalL hcalc 0
      (nativePrincipalTransposeJets
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))) := by
  have hm : ContDiff ℝ ∞ (fun t => coefficientMatrixMultiplierL hcalc 0
      (nativePrincipalTransposeJets
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))) := by
    apply contDiff_pi.mpr
    intro k
    apply contDiff_pi.mpr
    intro l
    exact contDiff_referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 i j l k
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

def referenceRotationAdjointMassForcingFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  (nativeCoefficientMassL hcalc
    (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)).comp nativeH2FirstOrderL

lemma contDiff_referenceRotationAdjointMassForcingFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (referenceRotationAdjointMassFunction g L Φ H w i j)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j)
  exact (hm.clm_comp contDiff_const).clm_comp contDiff_const

def referenceRotationAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) +
    (ordinaryPrincipalL hcalc 0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) -
      referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t) +
    referenceRotationAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t

lemma contDiff_referenceRotationAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) :=
  ((contDiff_referenceRotationTransposePrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).add
    ((contDiff_referenceRotationPrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).sub
      (contDiff_referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j))).add
        (contDiff_referenceRotationAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationPrincipalOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationTransposePrincipalOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMassForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointMassForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointOrdinaryStrongFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointOrdinaryStrongFamily
