import Calderon.FixedDirichletRegularity

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

/-- Apply a selected principal regularity conclusion at its literal native interface. -/
theorem exists_principal_regularity_lift
    (s : ℕ) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
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
    (f : BallSobolev s) (u : BallH1Zero)
    (hr : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := a) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) hcoeff u v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s f) v) :
    ∃ U : BallSobolev (s + 2),
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) U = (u : BallH1) ∧
      ‖U‖ ≤ c * (‖u‖ + ‖f‖) := by
  exact hregular f u hr


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
