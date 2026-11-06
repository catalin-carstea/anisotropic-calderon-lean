import Calderon.RadiusTwoNormalizedFixedOperatorOrderRegularity

/-! Full EXPANSION.json precedes source-free projection of the proved quantitative hreg conclusion. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma exists_radiusTwoNormalizedMetric_fixedOperator_order_lift
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) (s : ℕ)
    (f : BallSobolev s) (u : BallH1Zero)
    (hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) (TauCeti.Wkp.value s f) u) :
    ∃ U : BallSobolev (s+2), TauCeti.Wkp.firstOrder (s+1) U = (u : BallH1) := by
  trace "PROOFENTER source-free actual order lift projection"
  refine Exists.elim (exists_radiusTwoNormalizedMetric_fixedOperator_order_regularity hreg g hg s) ?_
  intro C hC
  trace "FACADE ELIMINATED source-free actual order lift projection"
  refine Exists.elim (hC.2 f u hWeak) ?_
  intro U hU
  trace "ABSTRACT SOLVE ELIMINATED source-free actual order lift projection"
  exact ⟨U,hU.1⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedMetric_fixedOperator_order_lift
