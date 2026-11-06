import Calderon.RadiusTwoNormalizedSmoothSourceCoherentOrderLifts
import Calderon.NativeAllOrderFirstOrderSmoothValue

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

lemma exists_radiusTwoNormalizedSmoothSource_contDiffOn_innerBall
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (F : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) a) ∧
      (TauCeti.W1p.value (radiusTwoNativeZeroDilation
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) : BallH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] G := by
  trace "PROOF ENTER actual smooth-source infinity tail"
  let u : BallH1 := (radiusTwoNativeZeroDilation
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F)) : BallH1)
  let P : ((s : ℕ) → BallSobolev (s+2)) → Prop := fun U =>
    (∀ s : ℕ, TauCeti.Wkp.firstOrder (s+1) (U s) = u) ∧
    (∀ s : ℕ, TauCeti.Wkp.lowerOrder (s+2) (U (s+1)) = U s)
  have hData : ∃ U : (s : ℕ) → BallSobolev (s+2), P U :=
    exists_coherent_radiusTwoNormalizedSmoothSource_order_lifts hreg g hg F
  trace "COHERENT PACKAGE MADE actual smooth-source infinity tail"
  refine Exists.elim hData ?_
  intro U hDataU
  trace "WITNESS ELIMINATED actual smooth-source infinity tail"
  have hU : ∀ s : ℕ, TauCeti.Wkp.firstOrder (s+1) (U s) = u := hDataU.1
  trace "FIRST ORDER TYPED actual smooth-source infinity tail"
  have hResult := exists_contDiffOn_innerBall_of_native_allOrder_firstOrder
    hcalc u U hU a ha ha1
  trace "GENERIC SMOOTH RESULT MADE actual smooth-source infinity tail"
  exact hResult
  trace "BODY COMPLETE actual smooth-source infinity tail"

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedSmoothSource_contDiffOn_innerBall
