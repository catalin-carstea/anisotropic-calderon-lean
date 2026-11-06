import Calderon.TauUniformDirichletInverse

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem unitBallDirichletForcing_injective : Function.Injective
    (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)) := by
  intro f g h
  have he : (fun z : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => ⟪f, z⟫_ℝ) =
      (fun z => ⟪g, z⟫_ℝ) :=
    TauCeti.W1p0.denseRange_valueL_two.equalizer
      (innerSL ℝ f).continuous (innerSL ℝ g).continuous (by
        funext v
        have hv := congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) h
        simpa only [Function.comp_apply, TauCeti.W1p0.valueL_apply,
          TauCeti.PDE.dirichletForcing_apply] using hv)
  have hz : ⟪f - g, f - g⟫_ℝ = 0 := by
    rw [inner_sub_left, congrFun he (f - g), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem unitBallDirichletForcing_eq_of_forall
    (f g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (h : ∀ v : BallH1Zero, TauCeti.PDE.dirichletForcing f v =
      TauCeti.PDE.dirichletForcing g v) : f = g :=
  unitBallDirichletForcing_injective (ContinuousLinearMap.ext h)

end OAI.AnisotropicCalderon.DirichletFamily
