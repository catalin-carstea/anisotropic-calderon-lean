import Calderon.RadiusTwoCanonicalPoleRoom
import Calderon.RadiusTwoActualInverseSourceRowExistence
import Calderon.RadiusTwoSingletonRepresentativeExtension
import Calderon.RadiusTwoCommonRowSymmetry

/-! EXPANSION.json precedes this actual symmetric inverse-source kernel assembly. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local irreducible] radiusTwoSourceSolution

theorem exists_radiusTwoSymmetricInverseSourceKernel
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2,
      ∃ G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ,
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
        (∀ p t : (radiusTwoOpens : Set R3), G p (t : R3) = G t (p : R3)) := by
  classical
  trace "PROOFENTER actual canonical symmetric inverse-source kernel"
  have hExist (p : (radiusTwoOpens : Set R3)) := exists_radiusTwoActualInverseSourceRow
    hreg hcalc g hg (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
      (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
      (radiusTwoCanonicalNormalizedPole_mem_room p)
  choose K G hLimit hCont hRep hBoundary hInv hPoint using hExist
  trace "ACTUAL ROW PAIRS CHOSEN ONCE AT ALL CANONICAL POLES"
  have hAE (p : (radiusTwoOpens : Set R3)) :
      (G p) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (K p : R3 → ℝ) := by
    apply radiusTwo_ae_eq_of_ae_eq_off_singleton (p : R3) (G p) (K p : R3 → ℝ)
    simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hRep p
  have hOpenCont (p : (radiusTwoOpens : Set R3)) :
      ContinuousOn (G p) ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • radiusTwoCanonicalNormalizedPole p}) := by
    apply (hCont p).mono
    intro z hz
    have hzBall : z ∈ ball (0 : R3) 2 := hz.1
    exact ⟨ball_subset_closedBall hzBall,hz.2⟩
  refine ⟨K,G,?_,?_⟩
  · intro p
    refine ⟨hLimit p,?_,hAE p,hBoundary p,?_,?_⟩
    · simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hCont p
    · intro f
      obtain ⟨F,hFC,hFA,hPair⟩ := hInv p f
      have hPairPhysical : (∫ z in radiusTwoOpens, K p z * f z ∂(volume : Measure R3)) =
          F (p : R3) := by
        simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hPair
      refine ⟨F,hFC,hFA,hPairPhysical,?_⟩
      calc
        (∫ z in radiusTwoOpens, G p z * f z ∂(volume : Measure R3)) =
            (∫ z in radiusTwoOpens, K p z * f z ∂(volume : Measure R3)) := by
          apply integral_congr_ae
          filter_upwards [hAE p] with z hz
          exact congrArg (fun v : ℝ => v * f z) hz
        _ = F (p : R3) := hPairPhysical
    · intro φ
      calc
        (∫ z in radiusTwoOpens, G p z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
            ∂(volume : Measure R3)) =
            (∫ z in radiusTwoOpens, K p z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
              ∂(volume : Measure R3)) := by
          apply integral_congr_ae
          filter_upwards [hAE p] with z hz
          exact congrArg (fun v : ℝ => v * (radiusTwoCompactMetricTestDensity g hg φ).1 z) hz
        _ = φ (p : R3) := by
          simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hPoint p φ
  · intro p t
    by_cases hpt : p = t
    · subst t
      rfl
    · have hNe : (2 : ℝ) • radiusTwoCanonicalNormalizedPole t ≠
          (2 : ℝ) • radiusTwoCanonicalNormalizedPole p := by
        rw [two_smul_radiusTwoCanonicalNormalizedPole,two_smul_radiusTwoCanonicalNormalizedPole]
        intro heq
        exact hpt (Subtype.ext heq.symm)
      have hSym := radiusTwoCommonRow_symmetry_of_continuous_representatives
        hreg hcalc g hg (radiusTwoCanonicalRoom p) (radiusTwoCanonicalRoom_pos p)
        (radiusTwoCanonicalRoom_lt_one p) (radiusTwoCanonicalNormalizedPole p)
        (radiusTwoCanonicalNormalizedPole_mem_room p) (K p) (hLimit p)
        (radiusTwoCanonicalRoom t) (radiusTwoCanonicalRoom_pos t)
        (radiusTwoCanonicalRoom_lt_one t) (radiusTwoCanonicalNormalizedPole t)
        (radiusTwoCanonicalNormalizedPole_mem_room t) (K t) (hLimit t)
        (G p) (G t) (hOpenCont p) (hOpenCont t) (hAE p).symm (hAE t).symm hNe
      simpa only [two_smul_radiusTwoCanonicalNormalizedPole] using hSym

end OAI.AnisotropicCalderon.ExteriorSource
