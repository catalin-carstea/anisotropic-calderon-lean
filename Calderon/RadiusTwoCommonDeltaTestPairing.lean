import Calderon.RadiusTwoCommonNormalizedDeltaSequence
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Analysis.Calculus.MeanValue

/-! EXPANSION.json precedes the literal common-bump test-pairing limit. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Gradient Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

theorem exists_radiusTwoCommonDeltaTest_pairing_bound
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      |(∫ z in radiusTwoOpens,
        radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z * φ z
          ∂(volume : Measure R3)) - φ ((2 : ℝ) • q)| ≤ (2*M) * (1/2 : ℝ)^n := by
  obtain ⟨M,hM,hVal,hGrad⟩ :=
    (φ.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le φ.hasCompactSupport
  refine ⟨M,hM,?_⟩
  intro n
  let ψ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n
  have hProps := radiusTwoCommonNormalizedDeltaSequence_properties a ha ha1 q hq n
  have hψInt : Integrable (ψ : R3 → ℝ) ((volume : Measure R3).restrict radiusTwoOpens) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).integrableOn
  have hProd : Integrable (fun z : R3 => ψ z * φ z)
      ((volume : Measure R3).restrict radiusTwoOpens) :=
    ((ψ.continuous.mul φ.continuous).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right).integrableOn
  have hDiff : Integrable (fun z : R3 => ψ z * (φ z - φ ((2 : ℝ) • q)))
      ((volume : Measure R3).restrict radiusTwoOpens) := by
    apply (hProd.sub (hψInt.mul_const (φ ((2 : ℝ) • q)))).congr
    apply Filter.Eventually.of_forall
    intro z
    change ψ z * φ z - ψ z * φ ((2 : ℝ) • q) = ψ z * (φ z - φ ((2 : ℝ) • q))
    ring
  have hPair : (∫ z in radiusTwoOpens, ψ z * φ z ∂(volume : Measure R3)) -
      φ ((2 : ℝ) • q) =
      ∫ z in radiusTwoOpens, ψ z * (φ z - φ ((2 : ℝ) • q)) ∂(volume : Measure R3) := by
    calc
      _ = (∫ z in radiusTwoOpens, ψ z * φ z ∂(volume : Measure R3)) -
          (∫ z in radiusTwoOpens, ψ z * φ ((2 : ℝ) • q) ∂(volume : Measure R3)) := by
        rw [integral_mul_const,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,one_mul]
      _ = _ := by
        rw [← integral_sub hProd (hψInt.mul_const (φ ((2 : ℝ) • q)))]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
  have hBound : ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      |ψ z * (φ z - φ ((2 : ℝ) • q))| ≤ ((2*M) * (1/2 : ℝ)^n) * ψ z := by
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : ψ z = 0
    · simp only [hz,zero_mul,abs_zero,mul_zero,le_refl]
    · have hs : z ∈ tsupport (ψ : R3 → ℝ) := subset_tsupport _ hz
      have hDist := (hProps.2.2 z hs).2
      have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by rw [smul_smul]; norm_num
      have hDouble : dist z ((2 : ℝ) • q) = 2 * dist ((1/2 : ℝ) • z) q := by
        calc
          _ = dist ((2 : ℝ) • ((1/2 : ℝ) • z)) ((2 : ℝ) • q) :=
            congrArg (fun y : R3 => dist y ((2 : ℝ) • q)) hCancel.symm
          _ = _ := by rw [dist_smul₀]; norm_num
      have hLip : |φ z - φ ((2 : ℝ) • q)| ≤ M * dist z ((2 : ℝ) • q) := by
        have h := (convex_univ : Convex ℝ (Set.univ : Set R3)).norm_image_sub_le_of_norm_fderiv_le
          (fun x _ => φ.contDiff.differentiable (by simp) x)
          (fun x _ => by rw [← TauCeti.norm_gradient_eq_norm_fderiv]; exact hGrad x)
          (Set.mem_univ ((2 : ℝ) • q)) (Set.mem_univ z)
        simpa only [Real.norm_eq_abs,dist_eq_norm] using h
      have hMod : |φ z - φ ((2 : ℝ) • q)| ≤ (2*M) * (1/2 : ℝ)^n := by
        calc
          _ ≤ M * dist z ((2 : ℝ) • q) := hLip
          _ ≤ M * (2 * (1/2 : ℝ)^n) :=
            mul_le_mul_of_nonneg_left (by rw [hDouble]; exact mul_le_mul_of_nonneg_left hDist (by norm_num)) hM
          _ = _ := by ring
      rw [abs_mul,abs_of_nonneg (hProps.1 z)]
      exact (mul_le_mul_of_nonneg_left hMod (hProps.1 z)).trans_eq (mul_comm _ _)
  change |(∫ z in radiusTwoOpens, ψ z * φ z ∂(volume : Measure R3)) - φ ((2 : ℝ) • q)| ≤ _
  rw [hPair]
  calc
    _ ≤ ∫ z in radiusTwoOpens, |ψ z * (φ z - φ ((2 : ℝ) • q))|
        ∂(volume : Measure R3) := abs_integral_le_integral_abs
    _ ≤ ∫ z in radiusTwoOpens, ((2*M) * (1/2 : ℝ)^n) * ψ z
        ∂(volume : Measure R3) :=
      integral_mono_ae (by simpa only [Real.norm_eq_abs] using hDiff.norm) (hψInt.const_mul _) hBound
    _ = _ := by
      rw [integral_const_mul,show (∫ z in radiusTwoOpens, ψ z ∂(volume : Measure R3)) = 1 from hProps.2.1,mul_one]

theorem radiusTwoCommonDeltaTest_pairing_tendsto
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (φ : 𝓓(radiusTwoOpens, ℝ)) :
    Tendsto (fun n : ℕ => ∫ z in radiusTwoOpens,
      radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n z * φ z
        ∂(volume : Measure R3)) atTop (𝓝 (φ ((2 : ℝ) • q))) := by
  obtain ⟨M,hM,hBound⟩ := exists_radiusTwoCommonDeltaTest_pairing_bound a ha ha1 q hq φ
  have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hRight : Tendsto (fun n : ℕ => (2*M) * (1/2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply,mul_zero] using (tendsto_const_nhds.mul heps)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun n => norm_nonneg _) _ hRight
  intro n
  simpa only [Real.norm_eq_abs] using hBound n

end OAI.AnisotropicCalderon.ExteriorSource
