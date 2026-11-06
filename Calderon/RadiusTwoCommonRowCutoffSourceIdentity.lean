import Calderon.RadiusTwoNativeCutoffValueCompatibility
import Calderon.RadiusTwoCommonRowLocalizedSource

/-! EXPANSION.json precedes derived SAME-row cutoff identity with the existing solver. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoCommonRow_cutoff_eq_existing_source
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : R3 → ℝ) (v w : RadiusTwoH1Zero)
    (η : 𝓓(radiusTwoOpens, ℝ))
    (hV : (TauCeti.W1p.value (v : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η z * K z))
    (hW : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => χ z * K z))
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M) :
    (v : RadiusTwoH1) = (radiusTwoSourceSolution g hg
      (radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1)) : RadiusTwoH1) := by
  trace "PROOF ENTER derived SAME-row existing source identity"
  have hCompat := radiusTwoNativeCutoff_eq_of_same_value K ⟨η,η.contDiff⟩ χ v w
    hV hW hOne hM hAbs hGrad
  trace "NATIVE CUTOFF COMPATIBILITY MADE actual SAME-row source identity"
  have hSource := radiusTwoCommonRow_localized_eq_sourceSolution g hg a ha ha1 q hq K hLimit
    χ w hW η hOne hPole hM hAbs hGrad
  exact hCompat.symm.trans hSource

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonRow_cutoff_eq_existing_source
