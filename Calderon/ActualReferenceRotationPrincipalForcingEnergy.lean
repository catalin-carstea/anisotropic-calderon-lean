import Calderon.ActualReferenceRotationAdjointStrongOperator
import Calderon.ActualReferenceRotationStrongEnergy
import Calderon.ActualReferencePrincipalForcingEnergy
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

lemma referenceRotationOrdinaryPrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x)) 0 0
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) U v
  have hField := coefficientMatrixField_referenceRotationPrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j t
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceRotationTransposePrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) 0 0
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let F := referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc (nativePrincipalTransposeJets F) U v
  have hField := (coefficientMatrixField_nativePrincipalTransposeJets F).trans
    (congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
      (coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceRotationOrdinaryStrongFamily_zero_forcing_energy (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hO := referenceRotationOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc i j t U v
  have hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0
      (referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t U) =
      referenceRotationOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t U := TauCeti.Wkp.value_zero _
  exact (congrArg (fun f : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) f v) hValue).symm.trans hO

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOrdinaryPrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTransposePrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationOrdinaryStrongFamily_zero_forcing_energy
