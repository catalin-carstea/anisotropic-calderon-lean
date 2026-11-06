import Calderon.RadiusTwoNormalizedMetricUnitEllipticity
import Calderon.StrongDirichletDomain

/-! Full EXPANSION.json precedes direct actual arbitrary-order native weak/hreg conversion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoNormalizedMetric_order_weakEquation_for_hreg
    (g : MatrixField)
    (hcoeff : MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand
      (principalCoefficient (enlargedBallNormalizedMetric g 2) x) (0 : R3) (0 : ℝ)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (s : ℕ) (f : BallSobolev s) (u : BallH1Zero)
    (hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) (TauCeti.Wkp.value s f) u) :
    ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value s f) v := by
  trace "PROOFENTER actual order weak hreg conversion"
  intro v
  rw [TauCeti.PDE.energyFormH1L0_apply]
  trace "ENERGYAPPLY actual order weak hreg conversion"
  exact hWeak v

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedMetric_order_weakEquation_for_hreg
