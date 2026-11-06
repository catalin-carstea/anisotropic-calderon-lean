import Calderon.UnitBallEnergyEquality
import Calderon.CoerciveBilinearUniqueness

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

theorem eq_of_unitBall_energyFormH1_eq
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff))
    (u v : BallH1Zero)
    (h : ∀ w : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta (0 : R3 → ℝ) (u : BallH1) (w : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta (0 : R3 → ℝ) (v : BallH1) (w : BallH1)) : u = v := by
  let z : BallH1Zero := u-v
  have hsum : (z : BallH1) + (v : BallH1) = (u : BallH1) := by
    change (u : BallH1) - (v : BallH1) + (v : BallH1) = (u : BallH1)
    exact sub_add_cancel _ _
  have hadd := TauCeti.PDE.energyFormH1_add_left
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff
    (z : BallH1) (z : BallH1) (v : BallH1)
  rw [hsum] at hadd
  have hscalar : TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (0 : R3 → ℝ) (z : BallH1) (z : BallH1) = 0 := by
    have he := h z
    linarith only [hadd,he]
  have hzero : TauCeti.PDE.energyFormH1L0
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff z z = 0 :=
    Eq.trans (α := ℝ) (unitBall_energyFormH1L0_apply a beta hcoeff z z) hscalar
  by_contra huv
  obtain ⟨c,hcpos,hcoercive⟩ := hc
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  have hle : c * ‖z‖ * ‖z‖ ≤ 0 := (hcoercive z).trans_eq hzero
  exact (not_lt_of_ge hle) (mul_pos (mul_pos hcpos hp) hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
