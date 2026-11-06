import Calderon.RadiusTwoNormalizedFixedOperatorOrderLift
import Calderon.RadiusTwoNormalizedSmoothSourceOrderWeakEquation

/-! Full EXPANSION.json precedes the SAME actual smooth-source solution order lift. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation radiusTwoNativeL2Dilation

run_cmd Lean.logInfo "BEFORE HEADER thin actual smooth-source order lift"

lemma exists_radiusTwoNormalizedSmoothSource_order_lift
    (hreg : FixedDirichletRegularity) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (s : ℕ) (F : SmoothData) :
    ∃ U : BallSobolev (s+2), TauCeti.Wkp.firstOrder (s+1) U =
      (radiusTwoNativeZeroDilation
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) : BallH1) := by
  trace "PROOFENTER thin actual smooth-source order lift"
  have hWeak := radiusTwoNormalizedSmoothSource_order_weak_equation g hg s F
  trace "WEAK EQUATION MADE thin actual smooth-source order lift"
  have hResult := exists_radiusTwoNormalizedMetric_fixedOperator_order_lift hreg g hg s
    (smoothBallSobolev s (radiusTwoNormalizedSmoothForcing F))
    (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F))) hWeak
  trace "RESULT MADE thin actual smooth-source order lift"
  exact hResult

run_cmd Lean.logInfo "AFTER DECLARATION thin actual smooth-source order lift"

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedSmoothSource_order_lift
