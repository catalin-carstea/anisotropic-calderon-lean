import Calderon.RadiusTwoNormalizedWeakEquationHregConversion
import Calderon.RadiusTwoNormalizedMetricUnitEllipticity
import Calderon.FixedDirichletRegularity

/-! Full EXPANSION.json precedes specialization of the ORIGINAL retained hreg.
No radius-two source constructor or norm of an actual source occurs in this header. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoNormalizedMetric_fixedOperator_H2_regularity
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev 0) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet
        (principalCoefficient (enlargedBallNormalizedMetric g 2))
        (0 : R3 → R3) (0 : R3 → ℝ) f u →
      ∃ U : BallSobolev 2, TauCeti.Wkp.firstOrder 1 U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖) := by
  trace "PROOFENTER actual normalized fixed-operator H2 regularity"
  let g2 : MatrixField := enlargedBallNormalizedMetric g 2
  have hg2 : IsAdmissibleMetric g2 := isAdmissibleMetric_radiusTwoNormalized g hg
  obtain ⟨lam,Lam,hell⟩ := exists_unitEllipticity_radiusTwoNormalizedMetric g hg
  trace "ELLIPTICITY actual normalized fixed-operator H2 regularity"
  have hsmooth : ContDiffOn ℝ ∞ (principalCoefficient g2) (closedBall (0 : R3) 2) :=
    (contDiff_principalCoefficient g2 hg2).contDiffOn
  let hcoeff := memLp_metricEnergyIntegrand g2 hg2
  trace "COEFFICIENTS actual normalized fixed-operator H2 regularity"
  obtain ⟨C,hC,hSolve⟩ := hreg 0 (principalCoefficient g2) lam Lam hsmooth hell hcoeff
  trace "HREG actual normalized fixed-operator H2 regularity"
  refine ⟨C,hC,?_⟩
  intro f u hWeak
  have hEq := radiusTwoNormalizedMetric_weakEquation_for_hreg g hcoeff f u hWeak
  trace "NATIVE WEAK EQUATION actual normalized fixed-operator H2 regularity"
  exact hSolve f u hEq

end OAI.AnisotropicCalderon.ExteriorSource
