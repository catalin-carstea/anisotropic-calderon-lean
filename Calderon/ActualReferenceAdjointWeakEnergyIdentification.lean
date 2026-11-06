import Calderon.ActualReferenceAdjointWeakEnergyConstruction
import Calderon.ActualReferenceRotationWeakEnergy

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

attribute [local irreducible] referenceAdjointWeakEnergyFamily
  referenceAdjointFullWeakEnergyFamily nativeH1ZeroDualRestrictionL

lemma referenceAdjointWeakEnergyFamily_eq_nativeRestriction
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p =
      nativeH1ZeroDualRestrictionL.comp
        (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hRestriction : (nativeH1ZeroDualRestrictionL.comp
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)) u v =
      referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u (v : BallH1) :=
    nativeH1ZeroDualRestrictionL_apply
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u) v
  have hR := referenceAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v
  have hE := referenceAdjointFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u (v : BallH1)
  exact hR.trans (hE.symm.trans hRestriction.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakEnergyFamily_eq_nativeRestriction
