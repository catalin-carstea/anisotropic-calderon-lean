import Calderon.NativeSmoothCoefficientFullMassEnergy
import Calderon.ActualReferenceAdjointMassFamily
import Calderon.ActualReferenceAdjointStrongOperator
import Calderon.ClosedCoefficientMultiplier

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

def referenceAdjointPrincipalJetsFamily1 (p : ℝ × (R3 × ℝ)) : SmoothCoefficientMatrix 1 :=
  fun i j => commonSupportMatrixFamily 1 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p j i

lemma coefficientMatrixField_referenceAdjointPrincipalJetsFamily1 (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField 1 (referenceAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData p) =
      (fun x => (a (p,x))ᵀ) := by
  have he := coefficientMatrixField_commonSupportMatrixFamily 1 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p
  exact congrArg (fun A : MatrixField => fun x => (A x)ᵀ) he

def referenceAdjointDriftJetsFamily1 (p : ℝ × (R3 × ℝ)) : Fin 3 → SmoothCoefficientJets 1 :=
  fun i => commonSupportCoefficientFamily 1
    (fun q => -conformalReferenceWeightedFramedDrift g L Φ H w q i)
    (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1).neg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun q x hx => by
      rw [(jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 q x hx]
      simp) p

lemma nativeSmoothDriftField_referenceAdjointDriftJetsFamily1 (p : ℝ × (R3 × ℝ)) :
    nativeSmoothDriftField (referenceAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData p) =
      (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) := by
  funext x
  ext i
  exact coefficientValue_commonSupportCoefficientFamily 1
    (fun q => -conformalReferenceWeightedFramedDrift g L Φ H w q i)
    (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1).neg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun q y hy => by
      rw [(jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 q y hy]
      simp) p x

def referenceAdjointFullWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  nativeSmoothCoefficientFullMassEnergyL hcalc
    (referenceAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData p)
    (referenceAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData p)
    (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)

lemma referenceAdjointFullWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u v : BallH1) :
    referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ) (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x) u v := by
  let F := referenceAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData p
  let G := referenceAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData p
  let M := referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p
  have hMass : coefficientValue 1 M =
      (fun x => -nativeSupportedDriftDivergence
        (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x) :=
    funext (coefficientValue_referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)
  have hF := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (nativeSmoothDriftField G) (coefficientValue 1 M) u v)
    (coefficientMatrixField_referenceAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData p)
  have hG := congrArg (fun b : R3 → R3 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (a (p,x))ᵀ) b (coefficientValue 1 M) u v)
    (nativeSmoothDriftField_referenceAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData p)
  have hM := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (a (p,x))ᵀ)
    (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) c u v) hMass
  exact (nativeSmoothCoefficientFullMassEnergyL_apply hcalc F G M u v).trans (hF.trans (hG.trans hM))

lemma contDiff_referenceAdjointFullWeakEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  have hPrincipal (i j : Fin 3) : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 0
      (referenceAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData p i j)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 0 (fun q => a q j i)
      (contDiff_pi.mp (contDiff_pi.mp
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 j) i)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p x hx => by rw [(jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p x hx]; rfl)
  have hDrift (i : Fin 3) : ContDiff ℝ ∞ (fun p => coefficientMultiplier hcalc 0
      (referenceAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData p i)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
      (fun q => -conformalReferenceWeightedFramedDrift g L Φ H w q i)
      (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
        (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1).neg)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun p x hx => by rw [(jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p x hx]; simp)
  have hMass := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)
  unfold referenceAdjointFullWeakEnergyFamily nativeSmoothCoefficientFullMassEnergyL
    nativeSmoothCoefficientFullEnergyL nativeCoefficientMassL
  exact ((ContDiff.sum fun i hi => ContDiff.sum fun j hj =>
    contDiff_const.clm_comp ((hPrincipal i j).clm_comp contDiff_const)).add
      (ContDiff.sum fun i hi => contDiff_const.clm_comp ((hDrift i).clm_comp contDiff_const))).add
        (contDiff_const.clm_comp (hMass.clm_comp contDiff_const))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointPrincipalJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceAdjointPrincipalJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointDriftJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftField_referenceAdjointDriftJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointFullWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointFullWeakEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointFullWeakEnergyFamily
