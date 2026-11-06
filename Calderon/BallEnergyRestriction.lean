import Calderon.SmoothSobolevBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem energyFormH1L0_eq_energyFormH1_ball
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (v : BallH1) := by
  exact TauCeti.PDE.energyFormH1L0_apply
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff u v

end OAI.AnisotropicCalderon.EnergyBridge
