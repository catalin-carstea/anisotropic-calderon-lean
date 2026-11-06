import Calderon.StrongDirichletDomain
import Calderon.MetricSmooth

set_option maxSynthPendingDepth 10

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- The complete fixed-operator regularity statement (McLean composite).
Theorems that use it take this proposition as an explicit hypothesis; it is not an axiom. -/
def FixedDirichletRegularity : Prop :=
  ∀ (s : ℕ) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ),
    ContDiffOn ℝ ∞ a (Metric.closedBall 0 2) →
    TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam →
    ∀ (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev s) (u : BallH1Zero),
      (∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) v) →
      ∃ U : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (s + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖)


end OAI.AnisotropicCalderon.DirichletFamily
