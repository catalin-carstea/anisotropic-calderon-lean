import Calderon.ActualJointNativeTraceOperatorFamily
import Calderon.NativeHarmonicLiftExtension

/-! The completed low harmonic lift, before any higher-order boundary class
registrations. No native structure is replaced. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma contDiffAt_joint_referenceCompletedHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun u : ℝ × (R3 × ℝ) =>
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 u.1 u.2).comp
        (harmonicLiftCompletion hF)) p := by
  exact (contDiffAt_joint_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 p hLow).clm_comp
      (contDiffAt_const (c := harmonicLiftCompletion hF))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_joint_referenceCompletedHarmonicLiftFamily
