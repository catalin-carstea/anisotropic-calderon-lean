import Calderon.ActualReferenceCoordinateForcingFamily
import Calderon.CoefficientFirstJetsCommonSupport

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

/-! Upfront expansion: EXPANSION-actual-coordinate-forcing-correction-topology-joint-v001.md. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem contDiff_referenceCoordinateCommutatorForcingFamily
    (hcalc : FixedSobolevCalculus) (k : Fin 3) :
    ContDiff ℝ ∞ (referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k) := by
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K := closedBall (0 : R3) 3
  have hK : IsCompact K := isCompact_closedBall _ _
  have hcolumn (i : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (unitBallCoordinateGradientL i).comp
        (nativeCoefficientH1ProductL hcalc
          (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p i k))) := by
    have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 1
      (fun t => a t i k) (contDiff_pi.mp (contDiff_pi.mp h.1 i) k) K hK
      (fun p x hx => by rw [h.2.2.2.1 p x hx]; rfl)
    exact contDiff_const.clm_comp (contDiff_const.clm_comp hm)
  have hrow (j : Fin 3) : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (coefficientMultiplier hcalc 0 (coefficientFirstJets
        (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p k j))).comp
          (unitBallCoordinateGradientL j)) := by
    have hm := contDiff_coefficientMultiplier_coefficientFirstJets_commonSupport hcalc
      (fun t => a t k j) (contDiff_pi.mp (contDiff_pi.mp h.1 k) j) K hK
      (fun p x hx => by rw [h.2.2.2.1 p x hx]; rfl)
    exact hm.clm_comp contDiff_const
  have hdrift : ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
      (coefficientMultiplier hcalc 0
        (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p k)).comp
      (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))) := by
    have hm := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
      (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t k)
      (((EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff).comp hc.1) K hK
      (fun p x hx => by rw [hc.2 p x hx]; rfl)
    exact hm.clm_comp contDiff_const
  unfold referenceCoordinateCommutatorForcingFamily nativeCoordinateCommutatorForcingL
  exact ((ContDiff.sum (fun i hi => hcolumn i)).add
    (ContDiff.sum (fun j hj => hrow j))).sub hdrift

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
