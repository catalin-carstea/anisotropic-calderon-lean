import Calderon.RadiusTwoNormalizedCutoffOrderForcingDilation
import Calderon.RadiusTwoNormalizedNativeSourceEquation
import Calderon.RadiusTwoNormalizedFixedOperatorOrderLift

/-! EXPANSION-cutoff-source-order-lift.json precedes actual source order gain. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation radiusTwoNativeL2Dilation

lemma radiusTwoNormalizedCutoffSource_order_weak_equation
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (η : SmoothData)
    (w : RadiusTwoH1Zero) (U : BallSobolev (k+1))
    (hU : TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1)) :
    TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (TauCeti.Wkp.value k (radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U))
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg
        (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)))) := by
  trace "PROOF ENTER actual cutoff source order weak equation"
  let f : RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)
  let z : BallH1Zero := radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f)
  have hValue : TauCeti.Wkp.value k (radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U) =
      (4 : ℝ) • radiusTwoNativeL2Dilation f :=
    radiusTwoNormalizedCutoffOrderForcing_value_eq_dilation hcalc k g hg η w U hU
  trace "FORCING VALUE MADE actual cutoff source order weak equation"
  have hSource := isWeakSolutionDirichlet_radiusTwoSourceSolution_dilated g hg f
  trace "SOURCE EQUATION MADE actual cutoff source order weak equation"
  exact Eq.mp (congrArg (fun h : BallSobolev 0 => TauCeti.PDE.IsWeakSolutionDirichlet
    (principalCoefficient (enlargedBallNormalizedMetric g 2))
    (0 : R3 → R3) (0 : R3 → ℝ) h z) hValue.symm) hSource

lemma exists_radiusTwoNormalizedCutoffSource_order_lift
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData)
    (w : RadiusTwoH1Zero) (U : BallSobolev (k+1))
    (hU : TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1)) :
    ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V =
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg
        (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))) : BallH1) := by
  trace "PROOF ENTER actual cutoff source order lift"
  let f : BallSobolev k := radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U
  let z : BallH1Zero := radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg
    (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1)))
  have hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ) (TauCeti.Wkp.value k f) z :=
    radiusTwoNormalizedCutoffSource_order_weak_equation hcalc k g hg η w U hU
  trace "ACTUAL WEAK EQUATION MADE cutoff source order lift"
  exact exists_radiusTwoNormalizedMetric_fixedOperator_order_lift hreg g hg k f z hWeak

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedCutoffSource_order_weak_equation
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedCutoffSource_order_lift
