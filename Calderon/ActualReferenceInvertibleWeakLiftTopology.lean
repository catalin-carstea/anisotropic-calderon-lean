import Calderon.ActualReferenceWeakHalfLiftTopology
import Calderon.ActualReferenceWeakEnergyNativeTopology
import Calderon.NativeInvertibleWeakLiftTopology

/-! Upfront argument: EXPANSION-invertible-weak-endpoint-topology-author-v001.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem contDiffAt_referenceWeakHalfLiftFamily_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF) p := by
  unfold referenceWeakHalfLiftFamily
  apply contDiffAt_nativeHalfWeakLiftFormula_of_isInvertible (hF := hF) (p := p)
  · exact (contDiff_joint_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt
  · exact (contDiff_referenceWeakEnergyFamily_native
      g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt
  · exact hi


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceWeakHalfLiftFamily_of_isInvertible
