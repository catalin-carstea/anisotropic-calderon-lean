import Calderon.NativeH2CoefficientFluxGreen
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace ContDiff Classical
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] ordinaryPrincipalL ordinaryConormalTraceL

theorem ordinaryPrincipalL_zero_test_energy_eq_forcing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U)) v := by
  have hT : τ0.valueTraceL (v : BallH1) = 0 := valueTraceL_zeroDirichlet τ0 v
  have hB :
      ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),
          TauCeti.W1p.value (v : BallH1)⟫_ℝ +
        sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,
          τ0.valueTraceL (v : BallH1)⟫_ℝ =
      ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),
          TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
    rw [hT, inner_zero_right, mul_zero, add_zero]
  exact (ordinaryPrincipalL_full_test_energy_Green hcalc τ0 F U (v : BallH1)).trans
    (hB.trans (TauCeti.PDE.dirichletForcing_apply
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U)) v).symm)

theorem dirichletForcing_neg_native
    (p : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (-p) v =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) p v := by
  rw [TauCeti.PDE.dirichletForcing_apply, TauCeti.PDE.dirichletForcing_apply]
  exact inner_neg_left p (TauCeti.W1p.value (v : BallH1))

theorem ordinaryPrincipalL_zero_test_energy_eq_neg_forcing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (U : BallSobolev 2)
    (p : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hp : TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U) = -p) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) =
      -TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) p v := by
  have hP := congrArg (fun q : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) q v) hp
  exact (ordinaryPrincipalL_zero_test_energy_eq_forcing hcalc τ0 F U v).trans
    (hP.trans (dirichletForcing_neg_native p v))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_zero_test_energy_eq_forcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dirichletForcing_neg_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryPrincipalL_zero_test_energy_eq_neg_forcing
