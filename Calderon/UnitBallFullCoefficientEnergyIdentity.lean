import Calderon.CoefficientFormScalarEvaluation
import Calderon.NativeCoefficientWeakEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem coefficientFormL_jetLpL_apply_eq_energyFormH1
    (A : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) :
    coefficientFormL (J := ℝ × R3) ((volume : Measure R3).restrict ballOpens)
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens))
      (hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
        ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))) u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        A (0 : R3 → R3) (0 : R3 → ℝ) u v := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤ μ :=
    hcoeff.toLp (fun x => TauCeti.PDE.energyIntegrand (A x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
  have hBase : coefficientFormL μ (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens)) C u v =
      TauCeti.lpBilinearForm μ C
        (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) u)
        (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) v) :=
    coefficientFormL_apply_apply μ
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens)) C u v
  have hEnergy := TauCeti.PDE.energyFormH1L_apply (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := A) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff u v
  change TauCeti.lpBilinearForm μ C
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) u)
      (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens) v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A (0 : R3 → R3) (0 : R3 → ℝ) u v at hEnergy
  exact hBase.trans hEnergy

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientFormL_jetLpL_apply_eq_energyFormH1
