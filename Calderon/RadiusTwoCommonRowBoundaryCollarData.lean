import Calderon.RadiusTwoCollarRepresentativeCompatibility
import Calderon.RadiusTwoCompactPoleCutoff
import Calderon.RadiusTwoCommonLimitZeroCutoff
import Calderon.RadiusTwoCommonRowGlobalContinuousRepresentative
import Calderon.RadiusTwoCommonRowCollarWeakEquation

/-! Full EXPANSION.json precedes actual SAME-K source-specific boundary realization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge DirichletFamily TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonRow_native_boundary_collar_data
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K)) :
    ∃ b : ℝ, ∃ w : RadiusTwoH1Zero, ∃ G : R3 → ℝ,
      1 ≤ b ∧ b < 2 ∧
      ContinuousOn G ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) ∧
      G =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K : R3 → ℝ) ∧
      ContinuousOn G (radiusTwoCollarOpens b : Set R3) ∧
      (W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (radiusTwoCollarOpens b)] G ∧
      (∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens b) 2,
        energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
          (0 : R3 → R3) (0 : R3 → ℝ)
          (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
          (v : W1p (volume : Measure R3) (radiusTwoCollarOpens b) 2) = 0) := by
  have hqNorm : ‖q‖ < a := mem_ball_zero_iff.mp hq
  have hPoleNorm : ‖(2 : ℝ) • q‖ < 2 := by
    rw [norm_smul]
    norm_num
    linarith
  obtain ⟨b,chi,M,epsilon,delta,hb1,hPole,hb2,hCompact,hM,hAbs,hGrad,hOne,
      hepsilon,hNear,hdelta,hVan⟩ := exists_radiusTwo_compact_pole_cutoff q hPoleNorm
  refine Exists.elim (exists_radiusTwoCommonLimit_zero_cutoff
    g hg a ha ha1 q hq K hLimit chi hCompact M hM hAbs hGrad ⟨delta,hdelta,hVan⟩) ?_
  intro w hw
  refine Exists.elim (exists_radiusTwoCommonRow_continuous_representative
    hreg hcalc g hg a ha ha1 q hq K hLimit) ?_
  intro G hG
  have hSub := radiusTwoCollarOpens_subset_punctured q b hPole.le
  have hCont : ContinuousOn G (radiusTwoCollarOpens b : Set R3) := hG.1.mono hSub
  have hValue := native_zero_cutoff_collar_value_ae_of_row_representative
    q b hPole.le chi.1 w K G hw hG.2 hOne
  have hWeak : ∀ v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens b) 2,
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
        (v : W1p (volume : Measure R3) (radiusTwoCollarOpens b) 2) = 0 :=
    radiusTwoCommonRow_cutoff_collar_weak_equation
      g hg a ha ha1 q hq K hLimit chi.1 w hw b hb1 hPole.le hOne
  exact ⟨b,w,G,hb1,hb2,hG.1,hG.2,hCont,hValue,hWeak⟩

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_radiusTwoCommonRow_native_boundary_collar_data
