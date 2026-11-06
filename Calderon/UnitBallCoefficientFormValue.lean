import Calderon.CoefficientFormScalarEvaluation

/-! EXPANSION.json precedes this real-valued actual energy identity.
The whole-operator correspondence remains preserved/open separately. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem unitBallCoefficientFormL_apply_eq_energyFormH1
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    unitBallCoefficientFormL
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (v : BallH1) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤ μ :=
    hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
  have hBase : unitBallCoefficientFormL C u v =
      TauCeti.lpBilinearForm μ C (unitBallJetL u) (unitBallJetL v) :=
    coefficientFormL_apply_apply μ unitBallJetL C u v
  have hJet (w : BallH1Zero) : unitBallJetL w =
      TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) (w : BallH1) := rfl
  have hTransport : TauCeti.lpBilinearForm μ C (unitBallJetL u) (unitBallJetL v) =
      TauCeti.lpBilinearForm μ C
        (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) (u : BallH1))
        (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) (v : BallH1)) :=
    congrArg₂ (fun U V : Lp (ℝ × R3) 2 μ => TauCeti.lpBilinearForm μ C U V) (hJet u) (hJet v)
  have hEnergy := TauCeti.PDE.energyFormH1L_apply (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := A) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff (u : BallH1) (v : BallH1)
  change TauCeti.lpBilinearForm μ C
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) (u : BallH1))
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) (v : BallH1)) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (v : BallH1) at hEnergy
  exact hBase.trans (hTransport.trans hEnergy)

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoefficientFormL_apply_eq_energyFormH1
