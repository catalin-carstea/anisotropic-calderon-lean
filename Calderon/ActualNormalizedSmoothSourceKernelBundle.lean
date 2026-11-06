import Calderon.ActualTwoMetricPoleSectionCompactTest
import Calderon.ActualTwoMetricPhysicalVolumeNormalization

/-! Full EXPANSION.json precedes this same-witness logical assembly. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem exists_twoMetric_normalizedSmoothInverseSourceKernels_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ K₁ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G₁ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
        ∃ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
          ∃ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₁ hg₁ K₁ G₁ ∧
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₂ hg₂ K₂ G₂ ∧
            HasRadiusTwoPhysicalInverseSourcePairing g₁ hg₁ K₁ G₁ ∧
            HasRadiusTwoPhysicalInverseSourcePairing g₂ hg₂ K₂ G₂ ∧
            (∀ (y : (radiusTwoOpens : Set R3)) (φ : 𝓓(radiusTwoOpens, ℝ)),
              (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G₁ y z *
                (radiusTwoCompactMetricTestDensity g₁ hg₁ φ).1 z ∂(volume : Measure R3)) = φ (y : R3)) ∧
            (∀ (y : (radiusTwoOpens : Set R3)) (φ : 𝓓(radiusTwoOpens, ℝ)),
              (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G₂ y z *
                (radiusTwoCompactMetricTestDensity g₂ hg₂ φ).1 z ∂(volume : Measure R3)) = φ (y : R3)) ∧
            (∀ p : (radiusTwoOpens : Set R3),
              (p : R3) ∈ (exteriorAnnulusOpens : Set R3) →
              EqOn (G₁ p) (G₂ p) ((exteriorAnnulusOpens : Set R3) \ {(p : R3)})) := by
  obtain ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,hTest₁,hTest₂,hEq⟩ :=
    exists_twoMetric_separatelySmoothInverseSourceKernels_poleTest_exterior_eq
      hreg hcalc g₁ g₂ hg₁ hg₂ hΛ
  exact ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,
    IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing g₁ hg₁ K₁ G₁ hData₁.1,
    IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing g₂ hg₂ K₂ G₂ hData₂.1,
    hTest₁,hTest₂,hEq⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_twoMetric_normalizedSmoothInverseSourceKernels_exterior_eq
