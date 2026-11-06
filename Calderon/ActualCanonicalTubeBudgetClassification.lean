import Calderon.ActualCanonicalTubeBudgetRegion
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

theorem exists_unit_direction_tubeRadialLevel (M e0 sigma:ℝ) (z:R3×R3)
    (ht:0 < tubeHeight M e0 z.2) (hn:0 < ‖z.1-z.2‖) :
    ∃ w:R3,‖w‖=1 ∧ z.1=z.2+tubeRadius M e0 (tubeRadialLevel M e0 sigma z) sigma z.2 • w := by
  let w:R3 := ‖z.1-z.2‖⁻¹ • (z.1-z.2)
  have hw:‖w‖=1 := by
    dsimp only [w]
    rw [norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ hn.ne']
  have hpow:0 < tubeHeight M e0 z.2^(1+sigma) := Real.rpow_pos_of_pos ht _
  have hR:tubeRadius M e0 (tubeRadialLevel M e0 sigma z) sigma z.2=‖z.1-z.2‖ := by
    unfold tubeRadius tubeRadialLevel
    exact div_mul_cancel₀ _ hpow.ne'
  refine ⟨w,hw,?_⟩
  rw [hR]
  dsimp only [w]
  rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  abel

theorem interiorTubeRoom_high_level_mem_seed_or_band
    (M e0 sigma c0 B T0 amin CY lower upper:ℝ)
    (hc0:0 < c0) (hB:0 ≤ B) (hM:B+3 < M) (he0:0 ≤ e0) (hsigma:0 ≤ sigma) (hamin:0 < amin):
    ∀ z∈interiorTubeRoom M e0 B T0 CY lower upper,amin ≤ tubeRadialLevel M e0 sigma z →
      z∈interiorTubeSeed M e0 c0 B T0 CY lower upper ∨
        z∈unseededTubeBand M e0 sigma c0 B T0 amin (2/c0+1) := by
  intro z hz ha
  by_cases hCone:min (z.1 2) (z.2 2) < c0*‖z.1-z.2‖
  · exact Or.inl ⟨hz,hCone⟩
  · have ht:0 < tubeHeight M e0 z.2 := hz.1.1.2
    have ht1:1 ≤ tubeHeight M e0 z.2 := (tube_base_height he0 hM hz.2.1.le hz.2.2.le).1
    have hn:0 < ‖z.1-z.2‖ := by
      by_contra hh
      have hn0:‖z.1-z.2‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
      change amin ≤ ‖z.1-z.2‖/tubeHeight M e0 z.2^(1+sigma) at ha
      rw [hn0,zero_div] at ha
      linarith only [ha,hamin]
    obtain ⟨w,hw,hX⟩ := exists_unit_direction_tubeRadialLevel M e0 sigma z ht hn
    have haUpper:tubeRadialLevel M e0 sigma z ≤ 2/c0+1 := by
      by_contra hh
      have hlarge:2/c0+1 ≤ tubeRadialLevel M e0 sigma z := (not_le.mp hh).le
      have hMpos:0 < M := by linarith only [hM,hB]
      have hSeed:=tube_amax_level_in_seed hc0 hMpos.le he0 ht1 hsigma hlarge hw
      rw [← hX] at hSeed
      exact hCone hSeed
    refine Or.inr ⟨(tubeRadialLevel M e0 sigma z,z.2,w),⟨hw,hz.2.1.le,hz.2.2.le,ha,haUpper,?_⟩,?_⟩
    · rw [← hX]
      exact not_lt.mp hCone
    · exact Prod.ext hX.symm rfl

theorem interiorTubeRoom_subset_fixedSeparationSet
    (M e0 B T0 CY lower upper:ℝ) (hCY:0 < CY) (hlower:0 < lower) (hupper:0 < upper):
    ∃ Bound:ℝ,0 < Bound ∧
      interiorTubeRoom M e0 B T0 CY lower upper⊆fixedSeparationSet Bound lower := by
  refine ⟨CY+upper+1,by positivity,?_⟩
  intro z hz
  have hy:‖z.2‖ < CY := hz.1.1.1
  have hsep:lower < ‖z.1-z.2‖ ∧ ‖z.1-z.2‖ < upper := hz.1.2
  have hxn:=norm_add_le (z.1-z.2) z.2
  rw [sub_add_cancel] at hxn
  exact ⟨by linarith only [hxn,hsep.2,hy],by linarith only [hy,hupper],hsep.1.le⟩

theorem interiorTubeRoom_positive_height (M e0 B T0 CY lower upper:ℝ):
    interiorTubeRoom M e0 B T0 CY lower upper⊆{z | 0 < tubeHeight M e0 z.2} := by
  intro z hz
  exact hz.1.1.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
