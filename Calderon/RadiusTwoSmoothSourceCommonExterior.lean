import Calderon.RadiusTwoSmoothSourceResponse
import Calderon.ActualTwoMetricCompactExteriorSourceResponse

/-! Full upfront expansion precedes the literal chosen-response data bridge.
The original all-smooth minimal-energy hypothesis gives native source equality;
the SAME response representatives are identified by continuous AE uniqueness. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

theorem radiusTwoSmoothSourceResponse_eqOn_exterior
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    EqOn (radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f)
      (radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f) (exteriorAnnulusOpens : Set R3) := by
  have hNative := radiusTwoSourceSolution_common_exterior_value_ae_of_compact_tsupport
    g₁ g₂ hg₁ hg₂ hΛ ⟨f,f.contDiff⟩ f.hasCompactSupport
    (tsupport_fixedExteriorSourceTest_subset_annulus f)
  have hMu : (volume : Measure R3).restrict exteriorAnnulusOpens ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume exteriorAnnulusOpens_le_radiusTwoOpens
  have hRep₁ := ((radiusTwoSmoothSourceResponse_spec hreg hcalc g₁ hg₁ f).2.2.1).filter_mono (ae_mono hMu)
  have hRep₂ := ((radiusTwoSmoothSourceResponse_spec hreg hcalc g₂ hg₂ f).2.2.1).filter_mono (ae_mono hMu)
  have hAE : radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f
      =ᵐ[(volume : Measure R3).restrict exteriorAnnulusOpens]
        radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f := by
    filter_upwards [hRep₁,hNative,hRep₂] with x h₁ hN h₂
    exact h₁.symm.trans (hN.trans h₂)
  exact Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3)) hAE exteriorAnnulusOpens.isOpen
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g₁ hg₁ f).1.continuousOn
    (radiusTwoSmoothSourceResponse_spec hreg hcalc g₂ hg₂ f).1.continuousOn

theorem radiusTwoSmoothSourceResponse_exterior_family_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f)
    (p : R3) (hp : p ∈ (exteriorAnnulusOpens : Set R3)) :
    (fun f : 𝓓(fixedExteriorSourceOpens, ℝ) => radiusTwoSmoothSourceResponse hreg hcalc g₁ hg₁ f p) =
      (fun f : 𝓓(fixedExteriorSourceOpens, ℝ) => radiusTwoSmoothSourceResponse hreg hcalc g₂ hg₂ f p) := by
  funext f
  exact radiusTwoSmoothSourceResponse_eqOn_exterior hreg hcalc g₁ g₂ hg₁ hg₂ hΛ f hp

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_eqOn_exterior
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoSmoothSourceResponse_exterior_family_eq
