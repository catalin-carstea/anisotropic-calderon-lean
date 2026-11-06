import Calderon.RadiusTwoCommonLimitPointSource
import Calderon.RadiusTwoCompactMetricDensitySupport
import Calderon.RadiusTwoCompactTestTransposition

/-! EXPANSION.json precedes the derived fixed-row offpole weak equation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonRow_cutoff_offpole_weak_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : R3 → ℝ) (w : RadiusTwoH1Zero)
    (hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => χ z * K z))
    (φ : 𝓓(radiusTwoOpens, ℝ))
    (hOne : ∀ z ∈ tsupport (φ : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (φ : R3 → ℝ)) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (w : RadiusTwoH1) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) = 0 := by
  have hPoint := radiusTwoCommonSource_limit_pointSource g hg a ha ha1 q hq K hLimit φ
  have hφPole : φ ((2 : ℝ) • q) = 0 := by
    by_contra h
    exact hPole (subset_tsupport _ h)
  calc
    _ = ∫ z in radiusTwoOpens, (radiusTwoCompactMetricTestDensity g hg φ).1 z *
        TauCeti.W1p.value (w : RadiusTwoH1) z ∂(volume : Measure R3) :=
      radiusTwoCompactTest_energy_transposition g hg w φ
    _ = ∫ z in radiusTwoOpens, K z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
        ∂(volume : Measure R3) := by
      apply integral_congr_ae
      filter_upwards [hValue] with z hz
      by_cases hφ : z ∈ tsupport (φ : R3 → ℝ)
      · rw [hz,hOne z hφ,one_mul,mul_comm]
      · rw [radiusTwoCompactMetricTestDensity_eq_zero_of_notMem_tsupport g hg φ z hφ,
          zero_mul,mul_zero]
    _ = φ ((2 : ℝ) • q) := hPoint
    _ = 0 := hφPole

end OAI.AnisotropicCalderon.ExteriorSource
