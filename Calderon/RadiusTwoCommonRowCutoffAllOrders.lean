import Calderon.RadiusTwoCommonLimitTestCutoff
import Calderon.RadiusTwoCommonRowCutoffSourceIdentity
import Calderon.RadiusTwoNormalizedCutoffSourceOrderLift
import Calderon.RadiusTwoCommonRowCutoffOrderSuccessor

/-! EXPANSION.json precedes genuine finite native cutoff induction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

theorem exists_radiusTwoCommonRow_cutoff_all_orders
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ))
    (hPole : ∀ j : ℕ, (2 : ℝ) • q ∉ tsupport (η j : R3 → ℝ))
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1) :
    ∃ w : ℕ → RadiusTwoH1Zero,
      (∀ j : ℕ, (TauCeti.W1p.value (w j : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η j z * K z)) ∧
      ∀ n j : ℕ, ∃ U : BallSobolev (n+1),
        TauCeti.Wkp.firstOrder n U = (radiusTwoNativeZeroDilation (w j) : BallH1) := by
  trace "PROOF ENTER actual SAME-row finite all-order induction"
  let w : ℕ → RadiusTwoH1Zero := fun j => Classical.choose
    (exists_radiusTwoCommonLimit_test_cutoff g hg a ha ha1 q hq K hLimit (η j) (hPole j))
  have hw (j : ℕ) : (TauCeti.W1p.value (w j : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η j z * K z) :=
    Classical.choose_spec
      (exists_radiusTwoCommonLimit_test_cutoff g hg a ha ha1 q hq K hLimit (η j) (hPole j))
  trace "ACTUAL ZERO CUTOFF SEQUENCE MADE finite all-order induction"
  refine ⟨w,hw,?_⟩
  intro n
  induction n with
  | zero =>
      intro j
      refine ⟨(radiusTwoNativeZeroDilation (w j) : BallH1),?_⟩
      exact TauCeti.Wkp.firstOrder_zero _
  | succ n ih =>
      intro j
      trace "SUCCESSOR ENTER actual SAME-row finite all-order induction"
      have hData : ∃ U : BallSobolev (n+1), TauCeti.Wkp.firstOrder n U =
          (radiusTwoNativeZeroDilation (w (j+1)) : BallH1) := ih (j+1)
      refine Exists.elim hData ?_
      intro U hU
      trace "PRIOR ORDER WITNESS MADE actual SAME-row finite all-order induction"
      exact exists_radiusTwoCommonRow_cutoff_order_successor hreg hcalc n g hg
        a ha ha1 q hq K hLimit (η j) (η (j+1) : R3 → ℝ) (w j) (w (j+1))
        (hw j) (hw (j+1)) (hOne j) (hPole j) U hU

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoCommonRow_cutoff_all_orders
