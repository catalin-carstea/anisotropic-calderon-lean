import Calderon.RadiusTwoNormalizedDeltaTest
import Mathlib.Analysis.SpecificLimits.Normed

/-! EXPANSION.json precedes a literal common source sequence independent of g. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

def radiusTwoCommonNormalizedDeltaSequence
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) :=
  Classical.choose (exists_radiusTwoNormalizedDeltaTest a ha ha1 q hq ((1/2 : ℝ)^n)
    (pow_pos (by norm_num : (0 : ℝ) < 1/2) n))

theorem radiusTwoCommonNormalizedDeltaSequence_properties
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a) (n : ℕ) :
    (∀ z : R3, 0 ≤ radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z) ∧
      (∫ z in radiusTwoOpens, radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z
        ∂(volume : Measure R3)) = 1 ∧
      ∀ z ∈ tsupport (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n : R3 → ℝ),
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a ∧
          dist ((1/2 : ℝ) • z) q ≤ (1/2 : ℝ)^n :=
  Classical.choose_spec (exists_radiusTwoNormalizedDeltaTest a ha ha1 q hq ((1/2 : ℝ)^n)
    (pow_pos (by norm_num : (0 : ℝ) < 1/2) n))

theorem radiusTwoCommonNormalizedDeltaSequence_eventually_tsupport_exterior
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (hqE : (1/2 : ℝ) < ‖q‖) :
    ∀ᶠ n in atTop,
      tsupport (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n : R3 → ℝ) ⊆
        {z : R3 | 1 < ‖z‖ ∧ ‖z‖ < 2} := by
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  have hSmall : ∀ᶠ n in atTop, (1/2 : ℝ)^n < ‖q‖-(1/2 : ℝ) :=
    (tendsto_order.1 heps).2 _ (by linarith)
  filter_upwards [hSmall] with n hn
  exact radiusTwoDeltaTest_tsupport_subset_exterior
    (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n) q ((1/2 : ℝ)^n) hn
    (fun z hz => ((radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n).2.2 z hz).2)

end OAI.AnisotropicCalderon.ExteriorSource
