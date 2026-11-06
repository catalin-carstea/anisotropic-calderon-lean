import Calderon.ActualReferenceTwoAngleAdjointStrongOperator
import Calderon.ActualReferenceTwoAngleStrongEnergy
import Calderon.ActualReferencePrincipalForcingEnergy
/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-principal-forcing-v038.md. -/
set_option autoImplicit false
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

lemma referenceTwoAngleOrdinaryPrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x)) 0 0
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) U v
  have hField := coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceTwoAngleTransposePrincipalForcing_energy (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)) U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) 0 0
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  have hP := ordinaryPrincipalL_zero_forcing_energy hcalc (nativePrincipalTransposeJets F) U v
  have hField := (coefficientMatrixField_nativePrincipalTransposeJets F).trans
    (congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
      (coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
  exact hP.trans (congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1)) hField)

lemma referenceTwoAngleOrdinaryStrongFamily_zero_forcing_energy (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
        0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have hO := referenceTwoAngleOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U v
  have hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0
      (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U) =
      referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U := TauCeti.Wkp.value_zero _
  exact (congrArg (fun f : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) f v) hValue).symm.trans hO

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryPrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleTransposePrincipalForcing_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryStrongFamily_zero_forcing_energy
