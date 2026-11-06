import Calderon.RadiusTwoCommonDeltaTestPairing
import Calderon.RadiusTwoSourceReciprocity
import Calderon.RadiusTwoCompactMetricSourceIdentification

/-! EXPANSION.json precedes the point-source identity for the SAME actual L2 limit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoSource_pair_compactMetricTest
    (g : MatrixField) (hg : IsAdmissibleMetric g) (ρ : RadiusTwoL2)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg ρ : RadiusTwoH1),
      smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg φ)⟫_ℝ =
      ∫ z in radiusTwoOpens, ρ z * φ z ∂(volume : Measure R3) := by
  let f : RadiusTwoL2 := smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg φ)
  have hNative : TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) =
      TauCeti.testFunctionLp 2 φ := by
    have h := congrArg (fun w : RadiusTwoH1Zero => TauCeti.W1p.value (w : RadiusTwoH1))
      (radiusTwoSourceSolution_compactMetricTest g hg φ)
    exact h.trans (by rw [nativeZeroTestLinear_coe,TauCeti.W1p.value_ofTestFunctionₗ])
  have hAE : (TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (φ : R3 → ℝ) := by
    rw [hNative]
    exact TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ
  calc
    _ = ⟪ρ,TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1)⟫_ℝ :=
      (real_inner_comm _ _).trans (radiusTwoSourceSolution_reciprocity g hg ρ f).symm
    _ = ∫ z in radiusTwoOpens, ρ z *
        TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z
          ∂(volume : Measure R3) := by simp only [L2.inner_def,Real.inner_apply]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hAE] with z hz
      exact congrArg (fun t : ℝ => ρ z * t) hz

theorem radiusTwoCommonSource_limit_pointSource
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K)) :
    ∀ φ : 𝓓(radiusTwoOpens, ℝ),
      (∫ z in radiusTwoOpens, K z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
        ∂(volume : Measure R3)) = φ ((2 : ℝ) • q) := by
  intro φ
  let ψ (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ (n : ℕ) : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ n,(ψ n).contDiff⟩
  let f : RadiusTwoL2 := smoothRadiusTwoForcing (radiusTwoCompactMetricTestDensity g hg φ)
  have hPair (n : ℕ) :
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ =
        ∫ z in radiusTwoOpens, ψ n z * φ z ∂(volume : Measure R3) := by
    calc
      _ = ∫ z in radiusTwoOpens, ρ n z * φ z ∂(volume : Measure R3) :=
        radiusTwoSource_pair_compactMetricTest g hg (ρ n) φ
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [smoothRadiusTwoForcing_ae ⟨ψ n,(ψ n).contDiff⟩] with z hz
        exact congrArg (fun t : ℝ => t * φ z) hz
  have hLeft : Tendsto (fun n : ℕ =>
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ)
      atTop (𝓝 ⟪K,f⟫_ℝ) := hLimit.inner tendsto_const_nhds
  have hRight : Tendsto (fun n : ℕ =>
      ⟪TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1),f⟫_ℝ)
      atTop (𝓝 (φ ((2 : ℝ) • q))) :=
    (radiusTwoCommonDeltaTest_pairing_tendsto a ha ha1 q hq φ).congr'
      (Filter.Eventually.of_forall (fun n => (hPair n).symm))
  have hInner : ⟪K,f⟫_ℝ = φ ((2 : ℝ) • q) := tendsto_nhds_unique hLeft hRight
  have hLiteral :
      (∫ z in radiusTwoOpens, K z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
        ∂(volume : Measure R3)) = ⟪K,f⟫_ℝ := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [smoothRadiusTwoForcing_ae (radiusTwoCompactMetricTestDensity g hg φ)] with z hz
    exact congrArg (fun t : ℝ => K z * t) hz.symm
  exact hLiteral.trans hInner

end OAI.AnisotropicCalderon.ExteriorSource
