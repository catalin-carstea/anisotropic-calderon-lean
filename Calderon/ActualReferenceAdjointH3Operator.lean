import Calderon.ActualReferenceAdjointStrongOperator
import Calderon.NativeLowerOrderProjection
import Calderon.NativeCoefficientMultiplierOrderCoherence

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

/-- Order-three jets of the SAME jointly smooth reference principal matrix. -/
def referenceJointPrincipalJetsFamilyThree (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientMatrix 3 :=
  commonSupportMatrixFamily 3 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p

/-- Order-two jets of the exact negative drift divergence mass. -/
def referenceAdjointMassJetsFamilyTwo (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientJets 2 :=
  commonSupportCoefficientFamily 2 (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p

/-- The SAME full formal adjoint on H³→H¹: transpose principal,
negative original drift and its actual divergence mass. -/
def referenceAdjointOrdinaryStrongFamilyOne (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallSobolev 3 →L[ℝ] BallSobolev 1 :=
  ordinaryPrincipalL hcalc 1
      (fun i j => referenceJointPrincipalJetsFamilyThree g L y0 Φ B ε C ρ H a w hData p j i) +
    (ordinaryPrincipalL hcalc 1
        (referenceJointPrincipalJetsFamilyThree g L y0 Φ B ε C ρ H a w hData p) -
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2) +
    (coefficientMultiplier hcalc 1
      (referenceAdjointMassJetsFamilyTwo g L y0 Φ B ε C ρ H a w hData p)).comp
      ((nativeLowerOrderL 1).comp (nativeLowerOrderL 2))

lemma coefficientMatrixField_referenceJointPrincipalJetsFamilyThree
    (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField 3 (referenceJointPrincipalJetsFamilyThree
      g L y0 Φ B ε C ρ H a w hData p) = fun x => a (p,x) :=
  coefficientMatrixField_commonSupportMatrixFamily 3 a _ _ _ _ p

lemma coefficientValue_referenceAdjointMassJetsFamilyTwo
    (p : ℝ × (R3 × ℝ)) (x : R3) :
    coefficientValue 2 (referenceAdjointMassJetsFamilyTwo
      g L y0 Φ B ε C ρ H a w hData p) x =
      -nativeSupportedDriftDivergence
        (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x := by
  have h := coefficientValue_commonSupportCoefficientFamily 2
    (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p x
  exact h.trans (congrArg (fun t : ℝ => -t)
    (referenceWeightedDriftDivergence_eq_native g L y0 Φ B ε C ρ H a w hData p x))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
