import Calderon.ActualReferenceAdjointStrongOperator
import Calderon.ActualReferencePrincipalGlobalEllipticity
import Calderon.ActualReferenceStrongWeakHalfCoherence

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

lemma referenceOrdinaryPrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc
    (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) U v
  have hField := coefficientMatrixField_referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceTransposePrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p)) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (a (p,x))ᵀ) 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let F := referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc (nativePrincipalTransposeJets F) U v
  have hField := (coefficientMatrixField_nativePrincipalTransposeJets F).trans
    (congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
      (coefficientMatrixField_referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceOrdinaryStrongDriftFamily_zero_forcing_energy (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic g L y0 Φ B ε C ρ H a w hData p
  have hO := referenceOrdinaryStrongDriftFamily_energy_of_elliptic
    g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 lam Lam hUE U v
  have hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 U) =
      referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 U :=
    TauCeti.Wkp.value_zero _
  exact (congrArg (fun f : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) f v) hValue).symm.trans hO

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrdinaryPrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTransposePrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrdinaryStrongDriftFamily_zero_forcing_energy
