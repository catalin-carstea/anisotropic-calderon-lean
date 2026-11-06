import Calderon.ActualReferenceAdjointFullWeakEnergy
import Calderon.ActualReferenceAdjointWeakZeroEnergy

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

def referenceAdjointWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  ((ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL).comp
      (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)

lemma referenceAdjointWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) (v : BallH1Zero) :
    referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ) (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x) u (v : BallH1) :=
  referenceAdjointFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u (v : BallH1)

lemma referenceAdjointWeakEnergyFamily_restriction (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    (referenceAdjointWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL =
        referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (referenceAdjointWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p (u : BallH1) v).trans
    (referenceAdjointWeakZeroEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData τ0 hcalc p u v).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakEnergyFamily_restriction
