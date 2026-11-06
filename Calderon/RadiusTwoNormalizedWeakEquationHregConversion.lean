import Calderon.RadiusTwoNormalizedMetricUnitEllipticity
import Calderon.StrongDirichletDomain

/-! Full EXPANSION.json precedes actual normalized native operator equation transport. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

run_cmd Lean.logInfo "BEFORE HEADER actual normalized weak/hreg equation conversion"

theorem radiusTwoNormalizedMetric_weakEquation_for_hreg
    (g : MatrixField)
    (hcoeff : MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand
      (principalCoefficient (enlargedBallNormalizedMetric g 2) x) (0 : R3) (0 : ℝ)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (f : BallSobolev 0) (u : BallH1Zero)
    (hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) f u) :
    ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0 f) v := by
  trace "PROOFENTER actual normalized weak/hreg equation conversion"
  intro v
  rw [TauCeti.PDE.energyFormH1L0_apply,TauCeti.Wkp.value_zero]
  trace "APPLY REWRITE actual normalized weak/hreg equation conversion"
  exact hWeak v

end OAI.AnisotropicCalderon.ExteriorSource
