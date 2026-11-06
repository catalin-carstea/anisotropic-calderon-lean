import Calderon.RadiusTwoSymmetricInverseSourceKernelExistence
import Calderon.ActualCommonSourceExteriorContinuousEquality

/-! EXPANSION.json precedes this actual two-metric source-kernel consequence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] radiusTwoSourceSolution

/-- The complete already-derived actual symmetric inverse-source kernel payload. -/
def IsRadiusTwoSymmetricInverseSourceKernel
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ) : Prop :=
  (∀ p : (radiusTwoOpens : Set R3),
          Tendsto (fun n : ℕ => TauCeti.W1p.value
            (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
              ⟨radiusTwoCommonNormalizedDeltaSequence (radiusTwoCanonicalRoom p)
                (radiusTwoCanonicalRoom_pos p) (radiusTwoCanonicalRoom_lt_one p)
                (radiusTwoCanonicalNormalizedPole p) (radiusTwoCanonicalNormalizedPole_mem_room p) n,
                (radiusTwoCommonNormalizedDeltaSequence (radiusTwoCanonicalRoom p)
                  (radiusTwoCanonicalRoom_pos p) (radiusTwoCanonicalRoom_lt_one p)
                  (radiusTwoCanonicalNormalizedPole p)
                  (radiusTwoCanonicalNormalizedPole_mem_room p) n).contDiff⟩) : RadiusTwoH1))
            atTop (𝓝 (K p)) ∧
          ContinuousOn (G p) (closedBall (0 : R3) 2 \ {(p : R3)}) ∧
          (G p) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (K p : R3 → ℝ) ∧
          (∀ y : R3, ‖y‖ = 2 → G p y = 0 ∧ ContinuousAt (G p) y) ∧
          (∀ f : RadiusTwoL2, ∃ F : R3 → ℝ, Continuous F ∧
            (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
              (1/2 : ℝ) • z ∈ closedBall (0 : R3) (radiusTwoCanonicalRoom p) →
                F z = TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z) ∧
            (∫ z in radiusTwoOpens, K p z * f z ∂(volume : Measure R3)) = F (p : R3) ∧
            (∫ z in radiusTwoOpens, G p z * f z ∂(volume : Measure R3)) = F (p : R3)) ∧
          (∀ φ : 𝓓(radiusTwoOpens, ℝ),
            (∫ z in radiusTwoOpens, G p z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
              ∂(volume : Measure R3)) = φ (p : R3))) ∧
        (∀ p t : (radiusTwoOpens : Set R3), G p (t : R3) = G t (p : R3))

theorem exists_twoMetric_symmetricInverseSourceKernels_exterior_eq
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g₁ g₂ : MatrixField) (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ K₁ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G₁ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
        ∃ K₂ : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
          ∃ G₂ : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
            IsRadiusTwoSymmetricInverseSourceKernel g₁ hg₁ K₁ G₁ ∧
            IsRadiusTwoSymmetricInverseSourceKernel g₂ hg₂ K₂ G₂ ∧
            (∀ p : (radiusTwoOpens : Set R3),
              (p : R3) ∈ (exteriorAnnulusOpens : Set R3) →
              EqOn (G₁ p) (G₂ p) ((exteriorAnnulusOpens : Set R3) \ {(p : R3)})) := by
  classical
  trace "PROOFENTER actual two-metric exterior source-kernel families"
  obtain ⟨K₁,G₁,hRows₁,hSym₁⟩ := exists_radiusTwoSymmetricInverseSourceKernel hreg hcalc g₁ hg₁
  obtain ⟨K₂,G₂,hRows₂,hSym₂⟩ := exists_radiusTwoSymmetricInverseSourceKernel hreg hcalc g₂ hg₂
  trace "BOTH ACTUAL KERNEL FAMILIES CHOSEN ONCE"
  refine ⟨K₁,G₁,K₂,G₂,⟨hRows₁,hSym₁⟩,⟨hRows₂,hSym₂⟩,?_⟩
  intro p hpE
  have hpE' : (2 : ℝ) • radiusTwoCanonicalNormalizedPole p ∈
      (exteriorAnnulusOpens : Set R3) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hpE
  obtain ⟨hLimit₁,hC₁,hA₁,hB₁,hInv₁,hPoint₁⟩ := hRows₁ p
  obtain ⟨hLimit₂,hC₂,hA₂,hB₂,hInv₂,hPoint₂⟩ := hRows₂ p
  obtain ⟨F₁,F₂,hF₁,hF₂,hFA₁,hFA₂,hEqF⟩ :=
    exists_radiusTwoCommonSource_continuous_representatives_exterior_eq
      hreg hcalc g₁ g₂ hg₁ hg₂ hΛ
      (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
      (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
      (radiusTwoCanonicalNormalizedPole_mem_room p) hpE' (K₁ p) (K₂ p) hLimit₁ hLimit₂
  let U : Set R3 := (radiusTwoOpens : Set R3) \ {(p : R3)}
  have hNOpen : IsOpen (radiusTwoOpens : Set R3) := by
    change IsOpen (ball (0 : R3) 2)
    exact isOpen_ball
  have hUOpen : IsOpen U := IsOpen.sdiff hNOpen isClosed_singleton
  have hUClosed : U ⊆ closedBall (0 : R3) 2 \ {(p : R3)} := by
    intro z hz
    have hzBall : z ∈ ball (0 : R3) 2 := hz.1
    exact ⟨ball_subset_closedBall hzBall,hz.2⟩
  have hF₁U : ContinuousOn F₁ U := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hF₁
  have hF₂U : ContinuousOn F₂ U := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hF₂
  have hFA₁U : F₁ =ᵐ[(volume : Measure R3).restrict U] (K₁ p : R3 → ℝ) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hFA₁
  have hFA₂U : F₂ =ᵐ[(volume : Measure R3).restrict U] (K₂ p : R3 → ℝ) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hFA₂
  have hGA₁U : (G₁ p) =ᵐ[(volume : Measure R3).restrict U] (K₁ p : R3 → ℝ) :=
    hA₁.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
  have hGA₂U : (G₂ p) =ᵐ[(volume : Measure R3).restrict U] (K₂ p : R3 → ℝ) :=
    hA₂.filter_mono (ae_mono (Measure.restrict_mono_set (volume : Measure R3) diff_subset))
  have hGF₁ : EqOn (G₁ p) F₁ U :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3))
      (hGA₁U.trans hFA₁U.symm) hUOpen (hC₁.mono hUClosed) hF₁U
  have hGF₂ : EqOn (G₂ p) F₂ U :=
    Measure.eqOn_open_of_ae_eq (μ := (volume : Measure R3))
      (hGA₂U.trans hFA₂U.symm) hUOpen (hC₂.mono hUClosed) hF₂U
  have hEqF' : EqOn F₁ F₂ ((exteriorAnnulusOpens : Set R3) \ {(p : R3)}) := by
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hEqF
  intro z hz
  have hzU : z ∈ U := ⟨exteriorAnnulusOpens_le_radiusTwoOpens hz.1,hz.2⟩
  exact (hGF₁ hzU).trans ((hEqF' hz).trans (hGF₂ hzU).symm)

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.IsRadiusTwoSymmetricInverseSourceKernel
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_twoMetric_symmetricInverseSourceKernels_exterior_eq
