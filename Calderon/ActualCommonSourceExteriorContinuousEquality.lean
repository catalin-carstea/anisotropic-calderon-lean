import Calderon.ActualCommonSourceExteriorLimitEquality
import Calderon.RadiusTwoCommonRowGlobalContinuousRepresentative
import Calderon.LocalAEContinuousRepresentativeGluing

/-! Full EXPANSION.json precedes actual pointwise exterior equality of chosen rows. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem exists_radiusTwoCommonSource_continuous_representatives_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
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
    ∃ F₁ F₂ : R3 → ℝ,
      ContinuousOn F₁ ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) ∧
      ContinuousOn F₂ ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) ∧
      F₁ =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K₁ : R3 → ℝ) ∧
      F₂ =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K₂ : R3 → ℝ) ∧
      EqOn F₁ F₂ ((exteriorAnnulusOpens : Set R3) \ {(2 : ℝ) • q}) := by
  obtain ⟨F₁,hC₁,hA₁⟩ := exists_radiusTwoCommonRow_continuous_representative
    hreg hcalc g₁ hg₁ a ha ha1 q hq K₁ hLimit₁
  obtain ⟨F₂,hC₂,hA₂⟩ := exists_radiusTwoCommonRow_continuous_representative
    hreg hcalc g₂ hg₂ a ha ha1 q hq K₂ hLimit₂
  have hK := radiusTwoCommonSource_limits_exterior_ae_eq
    g₁ g₂ hg₁ hg₂ hΛ a ha ha1 q hq hpE K₁ K₂ hLimit₁ hLimit₂
  have hEOpen : IsOpen (exteriorAnnulusOpens : Set R3) := by
    change IsOpen {z : R3 | 1 < ‖z‖ ∧ ‖z‖ < 2}
    exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hUP : ((exteriorAnnulusOpens : Set R3) \ {(2 : ℝ) • q}) ⊆
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) := by
    intro z hz
    exact ⟨exteriorAnnulusOpens_le_radiusTwoOpens hz.1,hz.2⟩
  have hF₁ : F₁ =ᵐ[(volume : Measure R3).restrict
      ((exteriorAnnulusOpens : Set R3) \ {(2 : ℝ) • q})] (K₁ : R3 → ℝ) :=
    hA₁.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hUP))
  have hF₂ : F₂ =ᵐ[(volume : Measure R3).restrict
      ((exteriorAnnulusOpens : Set R3) \ {(2 : ℝ) • q})] (K₂ : R3 → ℝ) :=
    hA₂.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) hUP))
  have hKU : (K₁ : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict
      ((exteriorAnnulusOpens : Set R3) \ {(2 : ℝ) • q})] (K₂ : R3 → ℝ) :=
    hK.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
  refine ⟨F₁,F₂,hC₁,hC₂,hA₁,hA₂,?_⟩
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (hF₁.trans (hKU.trans hF₂.symm))
    (IsOpen.sdiff hEOpen isClosed_singleton) (hC₁.mono hUP) (hC₂.mono hUP)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoCommonSource_continuous_representatives_exterior_eq
