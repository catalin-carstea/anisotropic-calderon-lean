import Calderon.ActualTwoMetricSymmetricSourceKernels
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Full EXPANSION.json precedes the exact actual weighted source integral normalization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] radiusTwoSourceSolution

/-- The coordinate volume measure of the unchanged original metric density. -/
def radiusTwoMetricVolumeMeasure (g : MatrixField) : Measure R3 :=
  (volume : Measure R3).withDensity (fun z => ENNReal.ofReal (vol g z))

theorem setIntegral_radiusTwoMetricVolumeMeasure
    (g : MatrixField) (hg : IsAdmissibleMetric g) (k F : R3 → ℝ) :
    (∫ z in radiusTwoOpens, k z * F z ∂radiusTwoMetricVolumeMeasure g) =
      (∫ z in radiusTwoOpens, k z * (vol g z * F z) ∂(volume : Measure R3)) := by
  have hMeas : Measurable (fun z => ENNReal.ofReal (vol g z)) :=
    (continuous_vol g hg).measurable.ennreal_ofReal
  have hFinite : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      ENNReal.ofReal (vol g z) < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hN : MeasurableSet (radiusTwoOpens : Set R3) := by
    change MeasurableSet (ball (0 : R3) 2)
    exact measurableSet_ball
  calc
    (∫ z in radiusTwoOpens, k z * F z ∂radiusTwoMetricVolumeMeasure g) =
        (∫ z in radiusTwoOpens, (ENNReal.ofReal (vol g z)).toReal • (k z * F z)
          ∂(volume : Measure R3)) :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        (μ := (volume : Measure R3)) hMeas hFinite (fun z => k z * F z) hN
    _ = (∫ z in radiusTwoOpens, k z * (vol g z * F z) ∂(volume : Measure R3)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [ENNReal.toReal_ofReal (vol_pos g hg z).le]
        simp only [smul_eq_mul]
        ring)

theorem setIntegral_radiusTwoMetricVolumeMeasure_div_volume
    (g : MatrixField) (hg : IsAdmissibleMetric g) (k f : R3 → ℝ) :
    (∫ z in radiusTwoOpens, k z * (f z / vol g z) ∂radiusTwoMetricVolumeMeasure g) =
      (∫ z in radiusTwoOpens, k z * f z ∂(volume : Measure R3)) := by
  calc
    (∫ z in radiusTwoOpens, k z * (f z / vol g z) ∂radiusTwoMetricVolumeMeasure g) =
        (∫ z in radiusTwoOpens, k z * (vol g z * (f z / vol g z)) ∂(volume : Measure R3)) :=
      setIntegral_radiusTwoMetricVolumeMeasure g hg k (fun z => f z / vol g z)
    _ = (∫ z in radiusTwoOpens, k z * f z ∂(volume : Measure R3)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        have hv : vol g z ≠ 0 := ne_of_gt (vol_pos g hg z)
        field_simp [hv])

/-- Physical source integrals for precisely the actual native L2 forcing class. -/
def HasRadiusTwoPhysicalInverseSourcePairing
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ) : Prop :=
  ∀ (p : (radiusTwoOpens : Set R3)) (f : RadiusTwoL2),
    ∃ H : R3 → ℝ, Continuous H ∧
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) (radiusTwoCanonicalRoom p) →
          H z = TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z) ∧
      (∫ z in radiusTwoOpens, K p z * (f z / vol g z) ∂radiusTwoMetricVolumeMeasure g) = H (p : R3) ∧
      (∫ z in radiusTwoOpens, G p z * (f z / vol g z) ∂radiusTwoMetricVolumeMeasure g) = H (p : R3)

theorem IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) :
    HasRadiusTwoPhysicalInverseSourcePairing g hg K G := by
  intro p f
  obtain ⟨hLimit,hCont,hAE,hBoundary,hInverse,hPoint⟩ := hData.1 p
  obtain ⟨H,hHC,hHA,hK,hG⟩ := hInverse f
  refine ⟨H,hHC,hHA,?_,?_⟩
  · exact (setIntegral_radiusTwoMetricVolumeMeasure_div_volume g hg
      (K p : R3 → ℝ) (f : R3 → ℝ)).trans hK
  · exact (setIntegral_radiusTwoMetricVolumeMeasure_div_volume g hg
      (G p) (f : R3 → ℝ)).trans hG

theorem exists_twoMetric_physicallyNormalizedInverseSourceKernels_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ K₁ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G₁ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
        ∃ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
          ∃ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
            IsRadiusTwoSymmetricInverseSourceKernel g₁ hg₁ K₁ G₁ ∧
            IsRadiusTwoSymmetricInverseSourceKernel g₂ hg₂ K₂ G₂ ∧
            HasRadiusTwoPhysicalInverseSourcePairing g₁ hg₁ K₁ G₁ ∧
            HasRadiusTwoPhysicalInverseSourcePairing g₂ hg₂ K₂ G₂ ∧
            (∀ p : (radiusTwoOpens : Set R3),
              (p : R3) ∈ (exteriorAnnulusOpens : Set R3) →
              EqOn (G₁ p) (G₂ p) ((exteriorAnnulusOpens : Set R3) \ {(p : R3)})) := by
  obtain ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,hEq⟩ :=
    exists_twoMetric_symmetricInverseSourceKernels_exterior_eq hreg hcalc g₁ g₂ hg₁ hg₂ hΛ
  exact ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,
    IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing g₁ hg₁ K₁ G₁ hData₁,
    IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing g₂ hg₂ K₂ G₂ hData₂,hEq⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoMetricVolumeMeasure
#print axioms OAI.AnisotropicCalderon.ExteriorSource.setIntegral_radiusTwoMetricVolumeMeasure
#print axioms OAI.AnisotropicCalderon.ExteriorSource.setIntegral_radiusTwoMetricVolumeMeasure_div_volume
#print axioms OAI.AnisotropicCalderon.ExteriorSource.HasRadiusTwoPhysicalInverseSourcePairing
#print axioms OAI.AnisotropicCalderon.ExteriorSource.IsRadiusTwoSymmetricInverseSourceKernel.physicalSourcePairing
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_twoMetric_physicallyNormalizedInverseSourceKernels_exterior_eq
