import Calderon.RadiusTwoNormalizedOrderWeakEquationHregConversion
import Calderon.RadiusTwoNormalizedMetricUnitEllipticity
import Calderon.FixedDirichletRegularity

/-! Full EXPANSION.json precedes the original hreg specialization at an arbitrary actual order. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

run_cmd Lean.logInfo "BEFORE HEADER actual all-order fixed operator"

lemma exists_radiusTwoNormalizedMetric_fixedOperator_order_regularity
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev s) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet
        (principalCoefficient (enlargedBallNormalizedMetric g 2))
        (0 : R3 → R3) (0 : R3 → ℝ) (TauCeti.Wkp.value s f) u →
      ∃ U : BallSobolev (s+2), TauCeti.Wkp.firstOrder (s+1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  trace "PROOFENTER actual all-order fixed operator"
  let g2 : MatrixField := enlargedBallNormalizedMetric g 2
  have hg2 : IsAdmissibleMetric g2 := isAdmissibleMetric_radiusTwoNormalized g hg
  obtain ⟨lam,Lam,hell⟩ := exists_unitEllipticity_radiusTwoNormalizedMetric g hg
  have hsmooth : ContDiffOn ℝ ∞ (principalCoefficient g2) (closedBall (0 : R3) 2) :=
    (contDiff_principalCoefficient g2 hg2).contDiffOn
  let hcoeff := memLp_metricEnergyIntegrand g2 hg2
  trace "COEFFICIENTS actual all-order fixed operator"
  obtain ⟨C,hC,hSolve⟩ := hreg s (principalCoefficient g2) lam Lam hsmooth hell hcoeff
  trace "HREG COMPLETE actual all-order fixed operator"
  refine ⟨C,hC,?_⟩
  intro f u hWeak
  trace "NATIVE INPUTS actual all-order fixed operator"
  have hEq := radiusTwoNormalizedMetric_order_weakEquation_for_hreg g hcoeff s f u hWeak
  trace "NATIVE EQUATION actual all-order fixed operator"
  have hResult := hSolve f u hEq
  trace "FINAL RESULT MADE actual all-order fixed operator"
  exact hResult

run_cmd Lean.logInfo "AFTER DECLARATION actual all-order fixed operator"

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedMetric_fixedOperator_order_regularity
