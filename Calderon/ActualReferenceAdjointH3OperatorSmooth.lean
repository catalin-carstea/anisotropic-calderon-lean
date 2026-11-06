import Calderon.ActualReferenceAdjointH3Operator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- Smooth order-one full adjoint family for the SAME joint coefficients. -/
theorem contDiff_referenceAdjointOrdinaryStrongFamilyOne
    (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointOrdinaryStrongFamilyOne
      g L y0 Φ B ε C ρ H a w hData hcalc) := by
  let F := referenceJointPrincipalJetsFamilyThree g L y0 Φ B ε C ρ H a w hData
  let M := referenceAdjointMassJetsFamilyTwo g L y0 Φ B ε C ρ H a w hData
  have hFM : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc 1 (F p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 2
      (fun q => a q i j)
      (contDiff_pi.mp (contDiff_pi.mp
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i) j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p x hx => by rw [(jointReferenceStrongCoefficient_data
        g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p x hx]; rfl)
  have hFTM : ContDiff ℝ ∞
      (fun p => coefficientMatrixMultiplierL hcalc 1 (fun i j => F p j i)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 2
      (fun q => a q j i)
      (contDiff_pi.mp (contDiff_pi.mp
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 j) i)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p x hx => by rw [(jointReferenceStrongCoefficient_data
        g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p x hx]; rfl)
  have hP : ContDiff ℝ ∞ (fun p => ordinaryPrincipalL hcalc 1 (F p)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 1)
      (unitBallCoordinateDerivativeL hcalc 2)).contDiff.comp hFM
  have hPT : ContDiff ℝ ∞
      (fun p => ordinaryPrincipalL hcalc 1 (fun i j => F p j i)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc 1)
      (unitBallCoordinateDerivativeL hcalc 2)).contDiff.comp hFTM
  have hD : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData
        hcalc 1 p.1 p.2) :=
    contDiff_joint_referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1
  have hM : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 1 (M p)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (referenceAdjointMassFunction g L Φ H w)
      (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)
  change ContDiff ℝ ∞ (fun p =>
    ordinaryPrincipalL hcalc 1 (fun i j => F p j i) +
      (ordinaryPrincipalL hcalc 1 (F p) -
        referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2) +
      (coefficientMultiplier hcalc 1 (M p)).comp
        ((nativeLowerOrderL 1).comp (nativeLowerOrderL 2)))
  exact (hPT.add (hP.sub hD)).add (hM.clm_comp contDiff_const)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
