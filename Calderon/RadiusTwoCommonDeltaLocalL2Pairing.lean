import Calderon.RadiusTwoCommonNormalizedDeltaSequence

/-! EXPANSION.json precedes local L2/continuous representative pairing for the SAME common sources. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem radiusTwoCommonDelta_local_L2_pairing_tendsto
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (k : RadiusTwoL2) (O : Set R3) (hO : IsOpen O) (hp : (2 : ℝ) • q ∈ O)
    (F : R3 → ℝ) (hF : ContinuousAt F ((2 : ℝ) • q))
    (hAE : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      z ∈ O → k z = F z) :
    Tendsto (fun n : ℕ => ⟪smoothRadiusTwoForcing
      ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
        (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩,k⟫_ℝ)
      atTop (𝓝 (F ((2 : ℝ) • q))) := by
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  have hPhysEps : Tendsto (fun n : ℕ => (2 : ℝ)*(1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul heps :
      Tendsto (fun n : ℕ => (2 : ℝ)*(1/2 : ℝ)^n) atTop (𝓝 ((2 : ℝ)*0)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hFNear : ∀ᶠ z in 𝓝 ((2 : ℝ) • q),
      dist (F z) (F ((2 : ℝ) • q)) < ε/2 :=
    (Metric.tendsto_nhds.mp hF) (ε/2) (half_pos hε)
  have hOMem : ∀ᶠ z in 𝓝 ((2 : ℝ) • q), z ∈ O := IsOpen.mem_nhds hO hp
  have hNear : ∀ᶠ z in 𝓝 ((2 : ℝ) • q), z ∈ O ∧
      dist (F z) (F ((2 : ℝ) • q)) < ε/2 :=
    Filter.Eventually.and hOMem hFNear
  obtain ⟨δ,hδ,hδNear⟩ := Metric.mem_nhds_iff.mp hNear
  have hSmall : ∀ᶠ n in atTop, (2 : ℝ)*(1/2 : ℝ)^n < δ :=
    (tendsto_order.1 hPhysEps).2 _ hδ
  filter_upwards [hSmall] with n hn
  let ψ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  let ρ : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ,ψ.contDiff⟩
  have hProps := radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n
  have hρ := smoothRadiusTwoForcing_ae ⟨ψ,ψ.contDiff⟩
  have hψInt : Integrable (ψ : R3 → ℝ) ((volume : Measure R3).restrict radiusTwoOpens) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
  have hρProd : Integrable (fun z : R3 => ρ z * k z)
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    simpa only [Real.inner_apply] using (L2.integrable_inner (𝕜 := ℝ) ρ k)
  have hProd : Integrable (fun z : R3 => ψ z * k z)
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    apply hρProd.congr
    filter_upwards [hρ] with z hz
    exact congrArg (fun t : ℝ => t * k z) hz
  have hLiteral : ⟪ρ,k⟫_ℝ = ∫ z in radiusTwoOpens, ψ z * k z ∂(volume : Measure R3) := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [hρ] with z hz
    exact congrArg (fun t : ℝ => t * k z) hz
  have hDiff : Integrable (fun z : R3 => ψ z * (k z-F ((2 : ℝ) • q)))
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    apply (hProd.sub (hψInt.mul_const (F ((2 : ℝ) • q)))).congr
    exact Eventually.of_forall (fun z => by
      change ψ z * k z - ψ z * F ((2 : ℝ) • q) = ψ z * (k z-F ((2 : ℝ) • q))
      ring)
  have hPair : (∫ z in radiusTwoOpens, ψ z * k z ∂(volume : Measure R3))-F ((2 : ℝ) • q) =
      ∫ z in radiusTwoOpens, ψ z * (k z-F ((2 : ℝ) • q)) ∂(volume : Measure R3) := by
    calc
      _ = (∫ z in radiusTwoOpens, ψ z * k z ∂(volume : Measure R3)) -
          (∫ z in radiusTwoOpens, ψ z * F ((2 : ℝ) • q) ∂(volume : Measure R3)) := by
        rw [integral_mul_const,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,one_mul]
      _ = _ := by
        rw [← integral_sub hProd (hψInt.mul_const (F ((2 : ℝ) • q)))]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
  have hBound : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      |ψ z * (k z-F ((2 : ℝ) • q))| ≤ (ε/2)*ψ z := by
    filter_upwards [hAE] with z hz
    by_cases hψ : ψ z = 0
    · simp only [hψ,zero_mul,abs_zero,mul_zero,le_refl]
    · have hs : z ∈ tsupport (ψ : R3 → ℝ) := subset_tsupport _ hψ
      have hNormDist : dist z ((2 : ℝ) • q) = (2 : ℝ)*dist ((1/2 : ℝ) • z) q := by
        have hScale : z - (2 : ℝ) • q = (2 : ℝ) • ((1/2 : ℝ) • z-q) := by
          rw [smul_sub,smul_smul]
          norm_num
        rw [dist_eq_norm,hScale,norm_smul,Real.norm_eq_abs]
        norm_num [dist_eq_norm]
      have hPhysDist : dist z ((2 : ℝ) • q) ≤ (2 : ℝ)*(1/2 : ℝ)^n := by
        rw [hNormDist]
        exact mul_le_mul_of_nonneg_left ((hProps.2.2 z hs).2) (by norm_num)
      have hy : z ∈ ball ((2 : ℝ) • q) δ := hPhysDist.trans_lt hn
      have hLocal := hδNear hy
      have hMod : |k z-F ((2 : ℝ) • q)| ≤ ε/2 := by
        rw [hz hLocal.1]
        simpa only [Real.dist_eq] using hLocal.2.le
      rw [abs_mul,abs_of_nonneg (hProps.1 z)]
      exact (mul_le_mul_of_nonneg_left hMod (hProps.1 z)).trans_eq (mul_comm _ _)
  have hMain : |(∫ z in radiusTwoOpens, ψ z * k z ∂(volume : Measure R3))-F ((2 : ℝ) • q)| ≤ ε/2 := by
    rw [hPair]
    calc
      _ ≤ ∫ z in radiusTwoOpens, |ψ z * (k z-F ((2 : ℝ) • q))|
          ∂(volume : Measure R3) := abs_integral_le_integral_abs
      _ ≤ ∫ z in radiusTwoOpens, (ε/2)*ψ z ∂(volume : Measure R3) :=
        integral_mono_ae (by simpa only [Real.norm_eq_abs] using hDiff.norm) (hψInt.const_mul _) hBound
      _ = _ := by
        rw [integral_const_mul,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,mul_one]
  change dist ⟪ρ,k⟫_ℝ (F ((2 : ℝ) • q)) < ε
  rw [hLiteral,Real.dist_eq]
  exact hMain.trans_lt (half_lt_self hε)

end OAI.AnisotropicCalderon.ExteriorSource
