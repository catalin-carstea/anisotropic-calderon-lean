import Calderon.RadiusTwoCommonNormalizedDeltaSequence
import Calderon.RadiusTwoSourcePoleCutoffCompletion
import Calderon.RadiusTwoCutoffLimitValueIdentification

/-! Full EXPANSION.json precedes retention of the chosen common-limit row in actual zero cutoffs. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonLimit_zero_cutoff
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : SmoothData) (hCompact : HasCompactSupport χ.1)
    (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ.1 x| ≤ M)
    (hGrad : ∀ x : R3, ‖gradient χ.1 x‖ ≤ M)
    (hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → χ.1 z = 0) :
    ∃ w : RadiusTwoH1Zero,
      (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => χ.1 z * K z) := by
  let ψ (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let u (n : ℕ) : RadiusTwoH1 :=
    (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) : RadiusTwoH1)
  obtain ⟨δ,hδ,hVan⟩ := hVan
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  have hSmall : ∀ᶠ n in atTop, (1/2 : ℝ)^n < δ := (tendsto_order.1 heps).2 _ hδ
  have hAnn : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ.1 z * smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩ z = 0 := by
    filter_upwards [hSmall] with n hn
    filter_upwards [smoothRadiusTwoForcing_ae ⟨ψ n,(ψ n).contDiff⟩] with z hz
    by_cases hψ : ψ n z = 0
    · rw [hz,hψ,mul_zero]
    · have hDist := ((radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n).2.2 z
        (subset_tsupport _ hψ)).2
      rw [hVan z (hDist.trans_lt hn),zero_mul]
  obtain ⟨w,hw⟩ := exists_radiusTwoSource_poleCutoff_zero_limit g hg χ.1 χ.2 hCompact M hM hAbs hGrad
    (fun n : ℕ => smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) hAnn hLimit.cauchySeq
  refine ⟨w,?_⟩
  exact value_radiusTwoCutoff_limit_eq_mul χ hM (fun x _ => hAbs x) (fun x _ => hGrad x)
    u (w : RadiusTwoH1) K hLimit hw

end OAI.AnisotropicCalderon.ExteriorSource
