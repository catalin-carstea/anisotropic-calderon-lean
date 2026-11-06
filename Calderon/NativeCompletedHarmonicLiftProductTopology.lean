import Calderon.NativeCompletedHarmonicLiftTopology

/-! Pull the completed native low lift back along `fst`, in its original native context before higher class caches. -/
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

lemma contDiffAt_joint_referenceCompletedHarmonicLiftFamily_fst
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 z.1.1 z.1.2).comp
        (harmonicLiftCompletion hF)) (p,t) := by
  exact (contDiffAt_joint_referenceCompletedHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hLow).comp (p,t) contDiffAt_fst

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_joint_referenceCompletedHarmonicLiftFamily_fst
