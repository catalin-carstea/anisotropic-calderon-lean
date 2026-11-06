import Calderon.ActualTwoMetricCommonExteriorResponse

/-! EXPANSION.json was saved before this exact-source compact-exterior wrapper. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoSourceSolution_common_exterior_value_ae_of_compact_tsupport
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hCompact : HasCompactSupport F.1)
    (hSupport : tsupport F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    ∀ᵐ x ∂(volume : Measure R3).restrict exteriorAnnulusOpens,
      TauCeti.W1p.value (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1) x =
      TauCeti.W1p.value (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1) x := by
  have hNonzeroSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3) :=
    (subset_tsupport F.1).trans hSupport
  exact radiusTwoSourceSolution_common_exterior_value_ae g₁ g₂ hg₁ hg₂ hΛ F hCompact hNonzeroSupport

theorem radiusTwoSourceSolution_common_exterior_restriction_of_compact_tsupport
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (F : SmoothData) (hCompact : HasCompactSupport F.1)
    (hSupport : tsupport F.1 ⊆ (exteriorAnnulusOpens : Set R3)) :
    TauCeti.W1p.restrictL exteriorAnnulusOpens_le_radiusTwoOpens
      (radiusTwoSourceSolution g₁ hg₁ (smoothRadiusTwoForcing F) : RadiusTwoH1) =
    TauCeti.W1p.restrictL exteriorAnnulusOpens_le_radiusTwoOpens
      (radiusTwoSourceSolution g₂ hg₂ (smoothRadiusTwoForcing F) : RadiusTwoH1) := by
  have hNonzeroSupport : Function.support F.1 ⊆ (exteriorAnnulusOpens : Set R3) :=
    (subset_tsupport F.1).trans hSupport
  exact radiusTwoSourceSolution_common_exterior_restriction g₁ g₂ hg₁ hg₂ hΛ F hCompact hNonzeroSupport

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_common_exterior_value_ae_of_compact_tsupport
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSourceSolution_common_exterior_restriction_of_compact_tsupport
