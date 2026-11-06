import Calderon.ActualCanonicalTubeBudgetClassification
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

theorem exists_uniform_canonical_unseeded_tube_band_budget
    (S:KnownSideSourceData) (M e0 sigma c0 B T0 amin CY lower upper:ℝ)
    (hc0:0 < c0) (hB:0 ≤ B) (hM:B+3 < M) (he0:0 < e0) (hsigma:0 ≤ sigma) (hsigma1:sigma ≤ 1)
    (hamin:0 < amin) (hlower:lower < amin) (hupper:(2/c0+1)*max 1 T0^2 < upper)
    (hTop:1 < c0*amin*T0^sigma)
    (hCenter:∀ Y:R3,-B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ‖Y‖ < CY)
    (hStrict:∀ a:ℝ,∀ Y w:R3,‖w‖=1 → -B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 →
      amin ≤ a → a ≤ 2/c0+1 → ¬min ((Y+tubeRadius M e0 a sigma Y • w) 2) (Y 2) <
        c0*‖(Y+tubeRadius M e0 a sigma Y • w)-Y‖ →
      ProductHessianStrictAt (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ))
        (fun _:R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) (Y+tubeRadius M e0 a sigma Y • w) Y (tubePhase M e0 a sigma)):
    ∃ lambda0 C:ℝ,0 < lambda0 ∧ 0 < C ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,
      ProductSolutionOn S L lambda F (interiorTubeRoom M e0 B T0 CY lower upper) →
      ∀ N:ℝ,0 ≤ N → (∀ x∈interiorTubeSeed M e0 c0 B T0 CY lower upper,‖F x‖ ≤ N) →
      ∀ x∈unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1),‖F x‖ ≤ C*N := by
  obtain ⟨hU,hSeed⟩ := isOpen_interiorTubeRoom_and_seed M e0 c0 B T0 CY lower upper
  apply exists_uniform_actual_tube_compact_band_supremum_budget S M e0 sigma
    (unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1))
    (interiorTubeSeed M e0 c0 B T0 CY lower upper) (interiorTubeRoom M e0 B T0 CY lower upper)
    (isCompact_unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1) hsigma he0) hSeed hU
    (unseededTubeBand_subset_interiorTubeRoom M e0 sigma c0 B T0 amin CY lower upper
      hc0 hB hM he0.le hsigma hsigma1 hamin hlower hupper hTop hCenter)
    (interiorTubeRoom_positive_height M e0 B T0 CY lower upper) amin (2/c0+1) hamin.le
    (unseededTubeBand_radialLevel_bounds M e0 sigma c0 B T0 amin (2/c0+1) he0.le hM hamin)
    (interiorTubeRoom_high_level_mem_seed_or_band M e0 sigma c0 B T0 amin CY lower upper hc0 hB hM he0.le hsigma hamin)
  intro p hp _
  exact unseededTubeBand_flat_strictness M e0 sigma c0 B T0 amin (2/c0+1) he0.le hM hamin hStrict p hp

theorem fixedSeparationSet_subset_coarse_or_unseeded_tube_band
    (M e0 sigma c0 B d T0 amin CY lower upper:ℝ)
    (hc0:0 < c0) (hB:0 ≤ B) (hM:B+3 < M) (he0:0 ≤ e0) (hsigma:0 < sigma)
    (hT0:0 < T0) (hamin:0 < amin) (hLowerD:lower < d) (hUpperB:2*B < upper)
    (hTop:1 < c0*amin*T0^sigma)
    (hCenter:∀ Y:R3,-B-1 ≤ Y 2 → tubeHeight M e0 Y ≤ T0 → ‖Y‖ < CY)
    (hGap:∀ (D:ℝ) (Y:R3),d ≤ D → -B-1 ≤ Y 2 → Y 2 ≤ B → Y 0^2+Y 1^2 ≤ B^2 →
      amin < D/tubeHeight M e0 Y^(1+sigma)):
    ∀ q∈fixedSeparationSet B d,min (q.1 2) (q.2 2) < c0*‖q.1-q.2‖ ∨
      q∈unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1) := by
  intro q hq
  have hYCoord:|q.2 2| ≤ B := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le q.2 (2:Fin 3)).trans hq.2.1
  have hNormSq:‖q.2‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hq.2.1 2
  have hSq:‖q.2‖^2=q.2 0^2+q.2 1^2+q.2 2^2 := by
    simpa only [Fin.sum_univ_three] using EuclideanSpace.real_norm_sq_eq q.2
  have hHoriz:q.2 0^2+q.2 1^2 ≤ B^2 := by nlinarith only [hNormSq,hSq,sq_nonneg (q.2 2)]
  have hGapAt:amin < tubeRadialLevel M e0 sigma q := hGap ‖q.1-q.2‖ q.2 hq.2.2
    (by linarith only [(abs_le.mp hYCoord).1]) (abs_le.mp hYCoord).2 hHoriz
  have hSepUpper:‖q.1-q.2‖ < upper := (norm_sub_le q.1 q.2).trans_lt (by linarith only [hq.1,hq.2.1,hUpperB])
  rcases tube_target_in_room hc0 hsigma he0 hB hM hT0 hamin hTop (abs_le.mp hYCoord).1 hGapAt
    hCenter (hLowerD.trans_le hq.2.2) hSepUpper with hCone | hOutside
  · exact Or.inl hCone
  · have hInside:q∈interiorTubeRoom M e0 B T0 CY lower upper := ⟨hOutside.1,hOutside.2.1⟩
    rcases interiorTubeRoom_high_level_mem_seed_or_band M e0 sigma c0 B T0 amin CY lower upper
      hc0 hB hM he0 hsigma.le hamin q hInside hGapAt.le with hSeed | hBand
    · exact Or.inl hSeed.2
    · exact Or.inr hBand

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
