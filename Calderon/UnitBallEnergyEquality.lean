import Calderon.UnitBallEnergyEvaluation

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem unitBall_energyFormH1L0_apply_eq_of_energy_eq
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (u v w : BallH1Zero)
    (h : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta (0 : R3 → ℝ) (u : BallH1) (w : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta (0 : R3 → ℝ) (v : BallH1) (w : BallH1)) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff u w =
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff v w := by
  exact Eq.trans (α := ℝ)
    (unitBall_energyFormH1L0_apply a beta hcoeff u w)
    (Eq.trans (α := ℝ) h
      (Eq.symm (α := ℝ) (unitBall_energyFormH1L0_apply a beta hcoeff v w)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
