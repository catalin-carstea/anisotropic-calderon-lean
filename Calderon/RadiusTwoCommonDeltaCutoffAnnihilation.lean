import Calderon.RadiusTwoCommonNormalizedDeltaSequence
import Calderon.RadiusTwoNativeSourceFoundation

/-! Full EXPANSION.json precedes actual eventual annihilation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem radiusTwoCommonNormalizedDeltaSequence_eventually_annihilated
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (χ : SmoothData)
    (hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ.1 z = 0) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ.1 z * smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩ z = 0 := by
  let ψ (n : ℕ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  obtain ⟨δ,hδ,hVan⟩ := hVan
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  have hSmall : ∀ᶠ n in atTop, (1/2 : ℝ)^n < δ := (tendsto_order.1 heps).2 _ hδ
  filter_upwards [hSmall] with n hn
  filter_upwards [smoothRadiusTwoForcing_ae ⟨ψ n,(ψ n).contDiff⟩] with z hz
  by_cases hψ : ψ n z = 0
  · rw [hz,hψ,mul_zero]
  · have hDist := ((radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n).2.2 z
      (subset_tsupport _ hψ)).2
    rw [hVan z (hDist.trans_lt hn),zero_mul]

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonNormalizedDeltaSequence_eventually_annihilated
