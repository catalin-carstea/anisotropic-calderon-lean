import Calderon.ActualJointReferenceStrongInverse
import Calderon.ActualNativeTraceOperatorFamily
import Calderon.ActualReferenceInverseConsistency
import Calderon.SmoothCommonSupportStrongOperator
import Calderon.CompactInverseDerivativeBounds

/-! Source-only exact joint actual inverse topology on the same common weak
room. Joint coefficient maps are the native maps of the identical evaluated
spatial functions. No new operator or desired uniform inverse premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem referenceOrdinaryStrongDriftFamily_joint_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ) :
    (fun p : ℝ × (R3 × ℝ) =>
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2) =
      let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
      fun p : ℝ × (R3 × ℝ) =>
        ordinaryPrincipalL hcalc s
          (commonSupportMatrixFamily (s+2) a h.1
            (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p) +
        (-L*p.2.2) • ∑ i : Fin 3,
          (coefficientMultiplier hcalc s
            (commonSupportCoefficientFamily (s+1)
              (weightedDriftCoordinate w (conformalReferenceFramedDriftBase g L Φ H) i)
              (contDiff_weightedDriftCoordinate w h.2.1
                (conformalReferenceFramedDriftBase g L Φ H) h.2.2.1 i)
              (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
              (weightedDriftCoordinate_support w
                (conformalReferenceFramedDriftBase g L Φ H)
                (closedBall (0 : R3) 3) h.2.2.2.2 i) p)).comp
            (ordinaryLowerOrderCoordinateDerivativeL hcalc s i) := by
  funext p
  rfl

theorem contDiff_joint_referenceOrdinaryStrongDriftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2) := by
  rw [referenceOrdinaryStrongDriftFamily_joint_eq g L y0 Φ B ε C ρ H a w hData hcalc s]
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  have hm : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s+2) a h.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s+1)
      (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp h.1 i) j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p z hz => by rw [h.2.2.2.1 p z hz]; rfl)
  have hP : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) => ordinaryPrincipalL hcalc s
      (commonSupportMatrixFamily (s+2) a h.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p)) :=
    (coefficientDivergenceL (unitBallCoordinateDerivativeL hcalc s)
      (unitBallCoordinateDerivativeL hcalc (s+1))).contDiff.comp hm
  apply hP.add
  apply (contDiff_const.mul contDiff_snd.snd).smul
  apply ContDiff.sum
  intro i hi
  exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s
    (weightedDriftCoordinate w (conformalReferenceFramedDriftBase g L Φ H) i)
    (contDiff_weightedDriftCoordinate w h.2.1
      (conformalReferenceFramedDriftBase g L Φ H) h.2.2.1 i)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (weightedDriftCoordinate_support w (conformalReferenceFramedDriftBase g L Φ H)
      (closedBall (0 : R3) 3) h.2.2.2.2 i)).clm_comp contDiff_const

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
