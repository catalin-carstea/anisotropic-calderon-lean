import Calderon.RadiusTwoCommonNormalizedDeltaSequence

/-! Full EXPANSION.json precedes continuous pairing for the literal common probability source. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem radiusTwoCommonDelta_continuous_pairing_tendsto
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (F : R3 → ℝ) (hF : Continuous F) :
    Tendsto (fun n : ℕ => ∫ z in radiusTwoOpens,
      radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z * F ((1/2 : ℝ) • z)
        ∂(volume : Measure R3)) atTop (𝓝 (F q)) := by
  have hHalf : Continuous (fun z : R3 => (1/2 : ℝ) • z) := continuous_const_smul (1/2 : ℝ)
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hNear : ∀ᶠ y in 𝓝 q, dist (F y) (F q) < ε/2 :=
    (Metric.tendsto_nhds.mp (hF.tendsto q)) (ε/2) (half_pos hε)
  obtain ⟨δ,hδ,hδNear⟩ := Metric.mem_nhds_iff.mp hNear
  have hSmall : ∀ᶠ n in atTop, (1/2 : ℝ)^n < δ := (tendsto_order.1 heps).2 _ hδ
  filter_upwards [hSmall] with n hn
  let ψ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  have hProps := radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n
  have hψInt : Integrable (ψ : R3 → ℝ) ((volume : Measure R3).restrict radiusTwoOpens) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
  have hProd : Integrable (fun z : R3 => ψ z * F ((1/2 : ℝ) • z))
      ((volume : Measure R3).restrict radiusTwoOpens) :=
    ((ψ.continuous.mul (hF.comp hHalf)).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right).integrableOn
  have hDiff : Integrable (fun z : R3 => ψ z * (F ((1/2 : ℝ) • z)-F q))
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    apply (hProd.sub (hψInt.mul_const (F q))).congr
    apply Eventually.of_forall
    intro z
    change ψ z * F ((1/2 : ℝ) • z) - ψ z * F q = ψ z * (F ((1/2 : ℝ) • z)-F q)
    ring
  have hPair : (∫ z in radiusTwoOpens, ψ z * F ((1/2 : ℝ) • z) ∂(volume : Measure R3))-F q =
      ∫ z in radiusTwoOpens, ψ z * (F ((1/2 : ℝ) • z)-F q) ∂(volume : Measure R3) := by
    calc
      _ = (∫ z in radiusTwoOpens, ψ z * F ((1/2 : ℝ) • z) ∂(volume : Measure R3)) -
          (∫ z in radiusTwoOpens, ψ z * F q ∂(volume : Measure R3)) := by
        rw [integral_mul_const,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,one_mul]
      _ = _ := by
        rw [← integral_sub hProd (hψInt.mul_const (F q))]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
  have hBound : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      |ψ z * (F ((1/2 : ℝ) • z)-F q)| ≤ (ε/2)*ψ z := by
    apply Eventually.of_forall
    intro z
    by_cases hz : ψ z = 0
    · simp only [hz,zero_mul,abs_zero,mul_zero,le_refl]
    · have hs : z ∈ tsupport (ψ : R3 → ℝ) := subset_tsupport _ hz
      have hDist := (hProps.2.2 z hs).2
      have hy : (1/2 : ℝ) • z ∈ ball q δ := hDist.trans_lt hn
      have hMod : |F ((1/2 : ℝ) • z)-F q| ≤ ε/2 := by
        simpa only [Real.dist_eq] using (hδNear hy).le
      rw [abs_mul,abs_of_nonneg (hProps.1 z)]
      exact (mul_le_mul_of_nonneg_left hMod (hProps.1 z)).trans_eq (mul_comm _ _)
  have hMain : |(∫ z in radiusTwoOpens, ψ z * F ((1/2 : ℝ) • z) ∂(volume : Measure R3))-F q| ≤ ε/2 := by
    rw [hPair]
    calc
      _ ≤ ∫ z in radiusTwoOpens, |ψ z * (F ((1/2 : ℝ) • z)-F q)|
          ∂(volume : Measure R3) := abs_integral_le_integral_abs
      _ ≤ ∫ z in radiusTwoOpens, (ε/2)*ψ z ∂(volume : Measure R3) :=
        integral_mono_ae (by simpa only [Real.norm_eq_abs] using hDiff.norm) (hψInt.const_mul _) hBound
      _ = _ := by
        rw [integral_const_mul,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,mul_one]
  change dist (∫ z in radiusTwoOpens, ψ z * F ((1/2 : ℝ) • z) ∂(volume : Measure R3)) (F q) < ε
  rw [Real.dist_eq]
  exact hMain.trans_lt (half_lt_self hε)

end OAI.AnisotropicCalderon.ExteriorSource
