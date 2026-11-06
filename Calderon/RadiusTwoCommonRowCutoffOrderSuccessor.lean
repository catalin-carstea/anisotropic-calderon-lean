import Calderon.RadiusTwoCommonRowCutoffSourceIdentity
import Calderon.RadiusTwoNormalizedCutoffSourceOrderLift
import Calderon.NativeFirstOrderLiftTransport

/-! EXPANSION.json precedes the focused actual native successor transition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution radiusTwoNativeZeroDilation

lemma exists_radiusTwoCommonRow_cutoff_order_successor
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus) (k : ℕ)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (η : 𝓓(radiusTwoOpens, ℝ)) (χ : R3 → ℝ) (v w : RadiusTwoH1Zero)
    (hV : (TauCeti.W1p.value (v : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η z * K z))
    (hW : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => χ z * K z))
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ))
    (U : BallSobolev (k+1))
    (hU : TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1)) :
    ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V =
      (radiusTwoNativeZeroDilation v : BallH1) := by
  trace "PROOF ENTER focused actual SAME-row order successor"
  obtain ⟨M,hM,hAbs,hGrad⟩ :=
    (η.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le η.hasCompactSupport
  let f : RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1)
  have hSource : (v : RadiusTwoH1) = (radiusTwoSourceSolution g hg f : RadiusTwoH1) :=
    radiusTwoCommonRow_cutoff_eq_existing_source g hg a ha ha1 q hq K hLimit
      χ v w η hV hW hOne hPole hM (fun z _ => hAbs z) (fun z _ => hGrad z)
  trace "SOURCE ID MADE focused actual SAME-row order successor"
  have hZero : v = radiusTwoSourceSolution g hg f := Subtype.ext hSource
  have hNative : (radiusTwoNativeZeroDilation v : BallH1) =
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1) :=
    congrArg (fun z : RadiusTwoH1Zero => (radiusTwoNativeZeroDilation z : BallH1)) hZero
  have hGain : ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V =
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1) :=
    exists_radiusTwoNormalizedCutoffSource_order_lift hreg hcalc k g hg
      ⟨η,η.contDiff⟩ w U hU
  trace "ACTUAL GAIN MADE focused SAME-row order successor"
  exact nativeFirstOrderLift_transport (k+1)
    (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1)
    (radiusTwoNativeZeroDilation v : BallH1) hNative.symm hGain

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoCommonRow_cutoff_order_successor
