import Calderon.ActualReferenceWeakHalfLiftTopology
import Calderon.ActualReferenceWeakDirichletEvaluation
import Calderon.NativeSupportedAdjointWeakSolution
import Calderon.NativeZeroEnergyFlipSmoothness

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

def referenceAdjointWeakZeroEnergyFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).flip

lemma referenceAdjointWeakZeroEnergyFamily_apply (τ0 : UnitBallValueTrace)
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) (u v : BallH1Zero) :
    referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ)
        (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
        (u : BallH1) (v : BallH1) := by
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p
  let G := nativeSupportedDriftSmoothData beta hbeta
  have hb : nativeAdjointDriftField G = beta := nativeAdjointDriftField_supported_eq beta hbeta
  have hd : nativeDriftDivergence G = nativeSupportedDriftDivergence beta :=
    nativeDriftDivergence_supported_eq beta hbeta
  have ha : Continuous (fun x => a (p,x)) :=
    (SpatialJetFields.contDiff_spatial_slice a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 p).continuous
  have hGreen := energyFormH1_adjoint_zero_test τ0 (fun x => a (p,x)) G 0
    ha continuous_zero u (v : BallH1)
  have hGreenLiteral : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) beta 0 (v : BallH1) (u : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ) (-beta)
        (fun x => -nativeSupportedDriftDivergence beta x) (u : BallH1) (v : BallH1) := by
    have hNeg : (fun x : R3 => -beta x) = (-beta : R3 → R3) := by funext x; rfl
    simpa only [hb,hd,Pi.zero_apply,zero_sub,hNeg] using hGreen.symm
  exact (referenceWeakDirichletEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p v u).trans
    hGreenLiteral

attribute [local irreducible] referenceWeakDirichletEnergyFamily

lemma contDiff_referenceAdjointWeakZeroEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  unfold referenceAdjointWeakZeroEnergyFamily
  exact contDiff_nativeZeroEnergyFlipFamily
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc)
    (contDiff_joint_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc)

lemma referenceAdjointWeakZeroEnergyFamily_isInvertible (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (referenceAdjointWeakZeroEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible :=
  isInvertible_nativeZeroEnergyFlip _ hOriginal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakZeroEnergyFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakZeroEnergyFamily_apply

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointWeakZeroEnergyFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointWeakZeroEnergyFamily_isInvertible

