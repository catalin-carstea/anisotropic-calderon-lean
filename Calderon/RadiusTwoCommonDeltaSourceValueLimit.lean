import Calderon.RadiusTwoDeltaSourceRowL2Limit
import Calderon.RadiusTwoCommonNormalizedDeltaSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! EXPANSION.json precedes convergence for one literal common source sequence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem exists_radiusTwoCommonDeltaSource_value_limit
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a) :
    ∃ K : RadiusTwoL2, Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K) := by
  obtain ⟨K,C,hC,hEstimate⟩ :=
    exists_radiusTwoDeltaSource_row_L2_estimate hreg hcalc g hg a ha ha1 q hq
  let ψ (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ (n : ℕ) : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩
  let α : NNReal := 1 - (Module.finrank ℝ R3 : NNReal) / 6
  have hα : (0 : ℝ) < (α : ℝ) := by norm_num [α,R3]
  have hProps (n : ℕ) := radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n
  have hBound (n : ℕ) :
      ‖TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)-K‖ ≤
        C * ((1/2 : ℝ)^n) ^ (α : ℝ) := by
    have hAE : (ρ n : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (ψ n : R3 → ℝ) := smoothRadiusTwoForcing_ae ⟨ψ n,(ψ n).contDiff⟩
    apply hEstimate ((1/2 : ℝ)^n) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n) (ρ n)
    · filter_upwards [hAE] with z hz
      rw [hz]
      exact (hProps n).1 z
    · exact (integral_congr_ae hAE).trans (hProps n).2.1
    · filter_upwards [hAE] with z hz hρ
      have hψ : ψ n z ≠ 0 := fun hzero => hρ (hz.trans hzero)
      exact (hProps n).2.2 z (subset_tsupport _ hψ)
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  have hPower : Tendsto (fun n : ℕ => ((1/2 : ℝ)^n) ^ (α : ℝ)) atTop (𝓝 0) := by
    have h := (Real.continuous_rpow_const hα.le).continuousAt.tendsto.comp heps
    simpa only [Function.comp_def,Real.zero_rpow hα.ne'] using h
  have hRight : Tendsto (fun n : ℕ => C * ((1/2 : ℝ)^n) ^ (α : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply,mul_zero] using (tendsto_const_nhds.mul hPower)
  refine ⟨K,?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero (fun _ => norm_nonneg _) hBound hRight

end OAI.AnisotropicCalderon.ExteriorSource
