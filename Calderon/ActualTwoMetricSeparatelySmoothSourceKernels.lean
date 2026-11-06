import Calderon.ActualTwoMetricSymmetricSourceKernels
import Calderon.RadiusTwoCommonRowOffPoleSmoothRepresentative

/-! Full EXPANSION.json precedes this SAME-family separate-smoothness supplement. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] radiusTwoSourceSolution
attribute [local instance] Classical.propDecidable

/-- An ambient pole section, used only for interior off-diagonal regularity. -/
def radiusTwoKernelPoleSection
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (y : (radiusTwoOpens : Set R3)) : R3 → ℝ :=
  fun x => if hx : x ∈ (radiusTwoOpens : Set R3) then G ⟨x,hx⟩ (y : R3) else 0

/-- The complete existing payload, with separate interior regularity attached. -/
def IsRadiusTwoSeparatelySmoothInverseSourceKernel
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ) : Prop :=
  IsRadiusTwoSymmetricInverseSourceKernel g hg K G ∧
    (∀ p : (radiusTwoOpens : Set R3),
      ContDiffOn ℝ ∞ (G p) ((radiusTwoOpens : Set R3) \ {(p : R3)})) ∧
    (∀ y : (radiusTwoOpens : Set R3),
      ContDiffOn ℝ ∞ (radiusTwoKernelPoleSection G y)
        ((radiusTwoOpens : Set R3) \ {(y : R3)}))

theorem IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) :
    IsRadiusTwoSeparatelySmoothInverseSourceKernel g hg K G := by
  classical
  trace "PROOFENTER SAME actual kernel separate smoothness"
  have hRows (p : (radiusTwoOpens : Set R3)) :
      ContDiffOn ℝ ∞ (G p) ((radiusTwoOpens : Set R3) \ {(p : R3)}) := by
    obtain ⟨hLimit,hC,hA,hB,hInv,hPoint⟩ := hData.1 p
    have hIn : ((radiusTwoOpens : Set R3) \ {(p : R3)}) ⊆
        closedBall (0 : R3) 2 \ {(p : R3)} := by
      intro x hx
      have hxBall : x ∈ ball (0 : R3) 2 := hx.1
      exact ⟨ball_subset_closedBall hxBall,hx.2⟩
    have hCont : ContinuousOn (G p) ((radiusTwoOpens : Set R3) \ {(p : R3)}) :=
      hC.mono hIn
    have hAE : (G p) =ᵐ[(volume : Measure R3).restrict
        ((radiusTwoOpens : Set R3) \ {(p : R3)})] (K p : R3 → ℝ) :=
      hA.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
    have hCont' : ContinuousOn (G p) ((radiusTwoOpens : Set R3) \
        {(2 : ℝ) • radiusTwoCanonicalNormalizedPole p}) := by
      simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hCont
    have hAE' : (G p) =ᵐ[(volume : Measure R3).restrict
        ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • radiusTwoCanonicalNormalizedPole p})]
          (K p : R3 → ℝ) := by
      simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hAE
    have hSmooth := contDiffOn_radiusTwoCommonRow_offpole_representative
      hreg hcalc g hg (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
      (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
      (radiusTwoCanonicalNormalizedPole_mem_room p) (K p) hLimit (G p) hCont' hAE'
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hSmooth
  trace "SAME SELECTED ACTUAL ROWS SMOOTH OFF POLE"
  refine ⟨hData,hRows,?_⟩
  intro y
  apply (hRows y).congr
  intro x hx
  unfold radiusTwoKernelPoleSection
  rw [dif_pos hx.1]
  exact hData.2 ⟨x,hx.1⟩ y

theorem exists_twoMetric_separatelySmoothInverseSourceKernels_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ K₁ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G₁ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
        ∃ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
          ∃ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₁ hg₁ K₁ G₁ ∧
            IsRadiusTwoSeparatelySmoothInverseSourceKernel g₂ hg₂ K₂ G₂ ∧
            (∀ p : (radiusTwoOpens : Set R3),
              (p : R3) ∈ (exteriorAnnulusOpens : Set R3) →
              EqOn (G₁ p) (G₂ p) ((exteriorAnnulusOpens : Set R3) \ {(p : R3)})) := by
  obtain ⟨K₁,G₁,K₂,G₂,hData₁,hData₂,hEq⟩ :=
    exists_twoMetric_symmetricInverseSourceKernels_exterior_eq hreg hcalc g₁ g₂ hg₁ hg₂ hΛ
  exact ⟨K₁,G₁,K₂,G₂,IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth hreg hcalc g₁ hg₁ K₁ G₁ hData₁,
    IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth hreg hcalc g₂ hg₂ K₂ G₂ hData₂,hEq⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoKernelPoleSection
#print axioms OAI.AnisotropicCalderon.ExteriorSource.IsRadiusTwoSeparatelySmoothInverseSourceKernel
#print axioms OAI.AnisotropicCalderon.ExteriorSource.IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_twoMetric_separatelySmoothInverseSourceKernels_exterior_eq
