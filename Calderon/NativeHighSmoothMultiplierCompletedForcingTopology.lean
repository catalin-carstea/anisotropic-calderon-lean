import Calderon.ActualHighSmoothMultiplierForcingJointTopology
import Calderon.NativeCompletedHarmonicLiftProductTopology

/-! Before-source v202: the literal native high forcing composed with the
completed low harmonic lift, in the original parent contexts. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (Kq : Set R3) (hKq : IsCompact Kq)
  (hqz : ∀ t x, x ∉ Kq → q (t,x) = 0)

open NativeHarmonicLiftCompletion

lemma contDiffAt_referenceHighSmoothMultiplierCompletedForcing_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      (referenceHighSmoothMultiplierCommutatorForcingFamily
        g L y0 Φ B ε C ρ H a w hData hcalc
        (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1).comp
          ((referenceHarmonicLiftFamily
            g L y0 Φ B ε C ρ H a w hData hcalc 0 z.1.1 z.1.2).comp
              (harmonicLiftCompletion hF))) (p,t) := by
  exact (contDiff_referenceHighSmoothMultiplierForcing_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc).contDiffAt.clm_comp
      (contDiffAt_joint_referenceCompletedHarmonicLiftFamily_fst
        g L y0 Φ B ε C ρ H a w hData hcalc hF p t hLow)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierCompletedForcing_commonSupport_joint
