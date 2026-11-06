import Calderon.SupportedDriftRegularityBase
import Calderon.SupportedDriftRegularityStep

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

theorem exists_supportedDrift_regularity_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev s) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet a beta 0 (TauCeti.Wkp.value s f) u →
      ∃ U : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (s + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  induction s with
  | zero =>
      exact exists_supportedDrift_regularity_bound_zero
        hcalc hreg a lam Lam hsmooth hUE hcoeff beta hbeta K hK hz
  | succ s ih =>
      exact exists_supportedDrift_regularity_bound_succ
        hcalc hreg a lam Lam hsmooth hUE hcoeff beta hbeta K hK hz s ih

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
