import Calderon.NativeSmoothCoefficientFullMassEnergy
import Calderon.ActualReferenceRotationAdjointMassFamily
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

def referenceRotationAdjointPrincipalJetsFamily1 (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : SmoothCoefficientMatrix 1 :=
  fun k l => referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j t l k

lemma coefficientMatrixField_referenceRotationAdjointPrincipalJetsFamily1 (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    coefficientMatrixField 1 (referenceRotationAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t) =
      (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) :=
  congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
    (coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j t)

def referenceRotationAdjointDriftJetsFamily1 (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : Fin 3 → SmoothCoefficientJets 1 :=
  fun k => commonSupportCoefficientFamily 1
    (fun q => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q k)
    (((EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1).neg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun q x hx => by
      rw [(referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 q x hx]
      simp) t

lemma nativeSmoothDriftField_referenceRotationAdjointDriftJetsFamily1 (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    nativeSmoothDriftField (referenceRotationAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t) =
      (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) := by
  funext x
  ext k
  exact coefficientValue_commonSupportCoefficientFamily 1
    (fun q => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q k)
    (((EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1).neg)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun q y hy => by
      rw [(referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 q y hy]
      simp) t x

def referenceRotationAdjointFullWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  nativeSmoothCoefficientFullMassEnergyL hcalc
    (referenceRotationAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t)
    (referenceRotationAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t)
    (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)

lemma referenceRotationAdjointFullWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) (u v : BallH1) :
    referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
        (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (fun x => -nativeSupportedDriftDivergence
          (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x) u v := by
  let F := referenceRotationAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t
  let G := referenceRotationAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t
  let M := referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t
  let A : MatrixField := fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  have hMass : coefficientValue 1 M = (fun x => -nativeSupportedDriftDivergence beta x) :=
    funext (coefficientValue_referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)
  have hF := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (nativeSmoothDriftField G) (coefficientValue 1 M) u v)
    (coefficientMatrixField_referenceRotationAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t)
  have hG := congrArg (fun b : R3 → R3 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A b (coefficientValue 1 M) u v)
    (nativeSmoothDriftField_referenceRotationAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t)
  have hM := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (fun x => -beta x) c u v) hMass
  exact (nativeSmoothCoefficientFullMassEnergyL_apply hcalc F G M u v).trans (hF.trans (hG.trans hM))

lemma contDiff_referenceRotationAdjointFullWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  have hPrincipal (k l : Fin 3) : ContDiff ℝ ∞ (fun t => coefficientMultiplier hcalc 0
      (referenceRotationAdjointPrincipalJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t k l)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
      (fun q => coordinateRotationPrincipalFamily i j a q l k)
      (contDiff_pi.mp (contDiff_pi.mp
        (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1 l) k)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun t x hx => by rw [(referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 t x hx]; rfl)
  have hDrift (k : Fin 3) : ContDiff ℝ ∞ (fun t => coefficientMultiplier hcalc 0
      (referenceRotationAdjointDriftJetsFamily1 g L y0 Φ B ε C ρ H a w hData i j t k)) :=
    contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
      (fun q => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q k)
      (((EuclideanSpace.proj k : R3 →L[ℝ] ℝ).contDiff.comp
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1).neg)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun t x hx => by rw [(referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 t x hx]; simp)
  have hMass := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (referenceRotationAdjointMassFunction g L Φ H w i j)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j)
  unfold referenceRotationAdjointFullWeakEnergyFamily nativeSmoothCoefficientFullMassEnergyL
    nativeSmoothCoefficientFullEnergyL nativeCoefficientMassL
  exact ((ContDiff.sum fun k hk => ContDiff.sum fun l hl =>
    contDiff_const.clm_comp ((hPrincipal k l).clm_comp contDiff_const)).add
      (ContDiff.sum fun k hk => contDiff_const.clm_comp ((hDrift k).clm_comp contDiff_const))).add
        (contDiff_const.clm_comp (hMass.clm_comp contDiff_const))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointPrincipalJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceRotationAdjointPrincipalJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointDriftJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftField_referenceRotationAdjointDriftJetsFamily1
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointFullWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointFullWeakEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointFullWeakEnergyFamily
