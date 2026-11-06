import Calderon.ActualJointOrdinaryStrongDrift
import Calderon.ActualReferenceAdjointMassFamily
import Calderon.NativeSupportedAdjointStrongForcing

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceJointPrincipalJetsFamily (p : ℝ × (R3 × ℝ)) : SmoothCoefficientMatrix 2 :=
  commonSupportMatrixFamily 2 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p

lemma coefficientMatrixField_referenceJointPrincipalJetsFamily (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField 2 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) =
      fun x => a (p,x) := coefficientMatrixField_commonSupportMatrixFamily 2 a _ _ _ _ p

lemma contDiff_referenceJointPrincipalOperatorFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (fun p => ordinaryPrincipalL hcalc 0
      (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc 0
      (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (fun q => a q i j)
      (contDiff_pi.mp (contDiff_pi.mp
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i) j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun t x hx => by rw [(jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 t x hx]; rfl)
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

lemma contDiff_referenceJointTransposePrincipalOperatorFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (fun p => ordinaryPrincipalL hcalc 0
      (nativePrincipalTransposeJets (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc 0
      (nativePrincipalTransposeJets (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (fun q => a q j i)
      (contDiff_pi.mp (contDiff_pi.mp
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 j) i)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun t x hx => by rw [(jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 t x hx]; rfl)
  exact (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 0)
    (unitBallCoordinateDerivativeL hcalc 1)).contDiff.comp hm

def referenceAdjointMassForcingFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  (nativeCoefficientMassL hcalc (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)).comp
    nativeH2FirstOrderL

lemma contDiff_referenceAdjointMassForcingFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)
  exact (hm.clm_comp contDiff_const).clm_comp contDiff_const

def referenceAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ordinaryPrincipalL hcalc 0
      (nativePrincipalTransposeJets (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) +
    (ordinaryPrincipalL hcalc 0 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) -
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2) +
    referenceAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc p

lemma contDiff_referenceAdjointOrdinaryStrongFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc) :=
  ((contDiff_referenceJointTransposePrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc).add
    ((contDiff_referenceJointPrincipalOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc).sub
      (contDiff_joint_referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0))).add
        (contDiff_referenceAdjointMassForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceJointPrincipalJetsFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceJointPrincipalJetsFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceJointPrincipalOperatorFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceJointTransposePrincipalOperatorFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMassForcingFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointMassForcingFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointOrdinaryStrongFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointOrdinaryStrongFamily
