import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels

/-! EXPANSION.json precedes the actual SAME-family pole-section compact-test identity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] radiusTwoSourceSolution

theorem IsRadiusTwoSymmetricInverseSourceKernel.poleSection_compactTest
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (y : (radiusTwoOpens : Set R3)) (φ : 𝓓(radiusTwoOpens, ℝ)) :
    (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G y z *
      (radiusTwoCompactMetricTestDensity g hg φ).1 z ∂(volume : Measure R3)) = φ (y : R3) := by
  classical
  have hEq : EqOn (radiusTwoKernelPoleSection G y) (G y) (radiusTwoOpens : Set R3) := by
    intro z hz
    unfold radiusTwoKernelPoleSection
    rw [dif_pos hz]
    exact hData.2 ⟨z,hz⟩ y
  have hN : MeasurableSet (radiusTwoOpens : Set R3) := by
    change MeasurableSet (ball (0 : R3) 2)
    exact measurableSet_ball
  obtain ⟨hLimit,hCont,hAE,hBoundary,hInverse,hPoint⟩ := hData.1 y
  calc
    (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G y z *
        (radiusTwoCompactMetricTestDensity g hg φ).1 z ∂(volume : Measure R3)) =
        (∫ z in radiusTwoOpens, G y z *
          (radiusTwoCompactMetricTestDensity g hg φ).1 z ∂(volume : Measure R3)) := by
      apply setIntegral_congr_fun hN
      intro z hz
      exact congrArg (fun v : ℝ => v * (radiusTwoCompactMetricTestDensity g hg φ).1 z) (hEq hz)
    _ = φ (y : R3) := hPoint φ

theorem exists_twoMetric_separatelySmoothInverseSourceKernels_poleTest_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ K₁ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G₁ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
        ∃ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
          ∃ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₁ hg₁ K₁ G₁ ∧
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₂ hg₂ K₂ G₂ ∧
            (∀ (y : (radiusTwoOpens : Set R3)) (φ : 𝓓(radiusTwoOpens, ℝ)),
              (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G₁ y z *
                (radiusTwoCompactMetricTestDensity g₁ hg₁ φ).1 z ∂(volume : Measure R3)) = φ (y : R3)) ∧
            (∀ (y : (radiusTwoOpens : Set R3)) (φ : 𝓓(radiusTwoOpens, ℝ)),
              (∫ z in radiusTwoOpens, radiusTwoKernelPoleSection G₂ y z *
                (radiusTwoCompactMetricTestDensity g₂ hg₂ φ).1 z ∂(volume : Measure R3)) = φ (y : R3)) ∧
            (∀ p : (radiusTwoOpens : Set R3),
              (p : R3) ∈ (exteriorAnnulusOpens : Set R3) →
              EqOn (G₁ p) (G₂ p) ((exteriorAnnulusOpens : Set R3) \ {(p : R3)})) := by
  obtain ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,hEq⟩ :=
    exists_twoMetric_separatelySmoothInverseSourceKernels_exterior_eq hreg hcalc g₁ g₂ hg₁ hg₂ hΛ
  refine ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,?_,?_,hEq⟩
  · intro y φ
    exact IsRadiusTwoSymmetricInverseSourceKernel.poleSection_compactTest
      g₁ hg₁ K₁ G₁ hData₁.1 y φ
  · intro y φ
    exact IsRadiusTwoSymmetricInverseSourceKernel.poleSection_compactTest
      g₂ hg₂ K₂ G₂ hData₂.1 y φ

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.IsRadiusTwoSymmetricInverseSourceKernel.poleSection_compactTest
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_twoMetric_separatelySmoothInverseSourceKernels_poleTest_exterior_eq
