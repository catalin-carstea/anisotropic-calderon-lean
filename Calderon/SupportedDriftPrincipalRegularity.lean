import Calderon.DriftSobolevConsistency
import Calderon.PrincipalRegularityApplication

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

theorem exists_supportedDrift_principal_regularity_lift
    (hcalc : FixedSobolevCalculus) (s : ℕ)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) (c : ℝ)
    (hregular : ∀ (f : BallSobolev s) (u : BallH1Zero),
      (∀ v : BallH1Zero,
        TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (a := a) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff u v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) s f) v) →
      ∃ U : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ c * (‖u‖ + ‖f‖))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (f : BallSobolev s) (u : BallH1Zero)
    (V : BallSobolev (s + 1))
    (hV : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) s V = (u : BallH1))
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) a beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s f) u) :
    ∃ U : BallSobolev (s + 2),
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) U = (u : BallH1) ∧
      ‖U‖ ≤ c * (‖u‖ + ‖f - supportedDriftL hcalc s beta hbeta K hK hz V‖) := by
  have hr : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := a) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff u v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s (f - supportedDriftL hcalc s beta hbeta K hK hz V)) v :=
    principal_equation_of_supportedDrift_weakSolution hcalc s a hcoeff
      beta hbeta K hK hz f u V hV hu
  exact exists_principal_regularity_lift
    (s := s) (a := a) (hcoeff := hcoeff) (c := c) (hregular := hregular)
    (f := (f - supportedDriftL hcalc s beta hbeta K hK hz V : BallSobolev s))
    (u := u) (hr := hr)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
