import Calderon.ActualTwoMetricCompactExteriorSourceResponse
import Calderon.RadiusTwoCommonNormalizedDeltaSequence

/-! Full EXPANSION.json precedes actual exterior AE equality of the SAME-sequence limits. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonSource_limits_exterior_ae_eq
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (hpE : (2 : ℝ) • q ∈ (exteriorAnnulusOpens : Set R3))
    (K₁ K₂ : RadiusTwoL2)
    (hLimit₁ : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K₁))
    (hLimit₂ : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K₂)) :
    (K₁ : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict exteriorAnnulusOpens] (K₂ : R3 → ℝ) := by
  have hqE : (1/2 : ℝ) < ‖q‖ := by
    have hLower : 1 < ‖(2 : ℝ) • q‖ := hpE.1
    rw [norm_smul,Real.norm_eq_abs] at hLower
    norm_num at hLower
    linarith
  let ψ (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let v₁ (n : ℕ) : RadiusTwoL2 := TauCeti.W1p.value
    (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) : RadiusTwoH1)
  let v₂ (n : ℕ) : RadiusTwoL2 := TauCeti.W1p.value
    (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩) : RadiusTwoH1)
  have hSupport := radiusTwoCommonNormalizedDeltaSequence_eventually_tsupport_exterior
    a ha ha1 q hq hqE
  have hResponse : ∀ᶠ n in atTop,
      (v₁ n : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict exteriorAnnulusOpens] (v₂ n : R3 → ℝ) := by
    filter_upwards [hSupport] with n hn
    exact radiusTwoSourceSolution_common_exterior_value_ae_of_compact_tsupport
      g₁ g₂ hg₁ hg₂ hΛ ⟨ψ n,(ψ n).contDiff⟩ (ψ n).hasCompactSupport hn
  have hc : (1 : ENNReal) ≠ (⊤ : ENNReal) := by simp
  have hμ : (volume : Measure R3).restrict exteriorAnnulusOpens ≤
      (1 : ENNReal) • (volume : Measure R3).restrict radiusTwoOpens := by
    simpa only [one_smul] using
      Measure.restrict_mono_set (volume : Measure R3) exteriorAnnulusOpens_le_radiusTwoOpens
  let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict exteriorAnnulusOpens) :=
    Lp.LpToLpOfMeasureLeSMul hc hμ
  have hR₁ : Tendsto (fun n : ℕ => R (v₁ n)) atTop (𝓝 (R K₁)) :=
    (R.continuous.tendsto K₁).comp hLimit₁
  have hR₂ : Tendsto (fun n : ℕ => R (v₂ n)) atTop (𝓝 (R K₂)) :=
    (R.continuous.tendsto K₂).comp hLimit₂
  have hEventually : (fun n : ℕ => R (v₁ n)) =ᶠ[atTop] (fun n : ℕ => R (v₂ n)) := by
    filter_upwards [hResponse] with n hn
    apply Lp.ext
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ (v₁ n)).trans
      (hn.trans (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ (v₂ n)).symm)
  have hR₁' : Tendsto (fun n : ℕ => R (v₂ n)) atTop (𝓝 (R K₁)) :=
    (tendsto_congr' hEventually).mp hR₁
  have hEq : R K₁ = R K₂ := tendsto_nhds_unique hR₁' hR₂
  have hEqAE : (R K₁ : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict exteriorAnnulusOpens]
      (R K₂ : R3 → ℝ) :=
    Eventually.of_forall (fun z => congrArg
      (fun v : Lp ℝ 2 ((volume : Measure R3).restrict exteriorAnnulusOpens) => v z) hEq)
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ K₁).symm.trans
    (hEqAE.trans (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ K₂))

end OAI.AnisotropicCalderon.ExteriorSource
