import Calderon.NativeCoefficientH1ProductDerivative
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem dirichletForcing_eq_of_scalar_product_ae
    (f f' : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (v v' : BallH1Zero) (m : R3 → ℝ)
    (hf : f' =ᵐ[(volume : Measure R3).restrict ballOpens] fun x => m x * f x)
    (hv : TauCeti.W1p.value (v' : BallH1) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => m x * TauCeti.W1p.value (v : BallH1) x) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f' v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v' := by
  have hL := TauCeti.PDE.dirichletForcing_apply_eq_setIntegral
    (mu := (volume : Measure R3)) (Omega := ballOpens) f' v
  have hR := TauCeti.PDE.dirichletForcing_apply_eq_setIntegral
    (mu := (volume : Measure R3)) (Omega := ballOpens) f v'
  apply hL.trans
  apply Eq.trans (b := ∫ x in (ballOpens : Set R3),
    f x * TauCeti.W1p.value (v' : BallH1) x)
  · apply integral_congr_ae
    filter_upwards [hf,hv] with x hfx hvx
    rw [hfx,hvx]
    ring
  · exact hR.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
