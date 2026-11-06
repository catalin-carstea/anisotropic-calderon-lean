import Calderon.RadiusTwoSourcePoleCutoffEnergy
import Calderon.RadiusTwoSourcePoleCutoffCompletion
import Calderon.RadiusTwoCutoffLimitValueIdentification
import Calderon.ActualTwoMetricSymmetricSourceKernels
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff Gradient InnerProductSpace Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoSource_localized_poleCutoff_graph_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (χ : SmoothData), HasCompactSupport χ.1 →
      ∀ (S : Set R3), MeasurableSet S → tsupport χ.1 ⊆ S →
      ∀ (M : ℝ) (hM : 0 ≤ M) (hAbs : ∀ x : R3, |χ.1 x| ≤ M)
      (hGrad : ∀ x : R3, ‖gradient χ.1 x‖ ≤ M) (f : RadiusTwoL2),
      (∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens, χ.1 x * f x = 0) →
      let u : RadiusTwoH1 := (radiusTwoSourceSolution g hg f : RadiusTwoH1)
      let w : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ.1 χ.2 hM
        (fun x _ => hAbs x) (fun x _ => hGrad x) u
      w ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 ∧
        ‖w‖ ^ 2 ≤ M ^ 2 * c *
          ∫ x in (radiusTwoOpens : Set R3) ∩ S, TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3) := by
  obtain ⟨lam, Lam, hlam, hLam, hEnergy⟩ := exists_radiusTwoSource_poleCutoff_energy_bound g hg
  let c : ℝ := 3 + 2 * (2 * Lam / lam) ^ 2
  refine ⟨c, by dsimp only [c]; positivity, ?_⟩
  intro χ hCompact S hS hSupp M hM hAbs hGrad f hAnn
  let u : RadiusTwoH1 := (radiusTwoSourceSolution g hg f : RadiusTwoH1)
  let w : RadiusTwoH1 := TauCeti.W1p.contDiffSMul χ.1 χ.2 hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) u
  let I : ℝ := ∫ x in (radiusTwoOpens : Set R3) ∩ S,
    TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3)
  have hValue : ‖TauCeti.W1p.value w‖ ^ 2 ≤ M ^ 2 * I := by
    have hRight : Integrable (S.indicator (fun x => TauCeti.W1p.value u x ^ 2))
        ((volume : Measure R3).restrict radiusTwoOpens) :=
      (TauCeti.W1p.integrable_value_sq u).indicator hS
    calc
      _ = ∫ x in radiusTwoOpens, TauCeti.W1p.value w x ^ 2 ∂(volume : Measure R3) :=
        (TauCeti.W1p.integral_value_sq_eq_norm_value_sq w).symm
      _ ≤ ∫ x in radiusTwoOpens, M ^ 2 * S.indicator
          (fun y => TauCeti.W1p.value u y ^ 2) x ∂(volume : Measure R3) := by
        apply integral_mono_ae (TauCeti.W1p.integrable_value_sq w) (hRight.const_mul (M ^ 2))
        filter_upwards [TauCeti.W1p.value_contDiffSMul_ae χ.2 hM
          (fun x _ => hAbs x) (fun x _ => hGrad x) u] with x hx
        by_cases hxS : x ∈ S
        · rw [indicator_of_mem hxS, hx, smul_eq_mul, mul_pow]
          have hχsq : χ.1 x ^ 2 ≤ M ^ 2 := by
            rw [← sq_abs (χ.1 x)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hAbs x) 2
          exact mul_le_mul_of_nonneg_right hχsq (sq_nonneg _)
        · have hχzero : χ.1 x = 0 :=
            (notMem_tsupport_iff_eventuallyEq.mp (fun h => hxS (hSupp h))).eq_of_nhds
          rw [indicator_of_notMem hxS, hx, hχzero]
          simp
      _ = M ^ 2 * I := by
        rw [integral_const_mul, setIntegral_indicator hS]
  have hWeighted : (∫ x in radiusTwoOpens, ‖gradient χ.1 x‖ ^ 2 *
      TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3)) ≤ M ^ 2 * I := by
    exact TauCeti.PDE.W1p.setIntegral_norm_gradient_sq_mul_value_sq_le u χ.2 hGrad hS hSupp
      (TauCeti.W1p.integrable_value_sq u) (Eventually.of_forall fun _ => le_rfl)
  have hGradient : ‖TauCeti.W1p.gradient w‖ ^ 2 ≤
      (2 * (2 * Lam / lam) ^ 2 + 2) * (M ^ 2 * I) := by
    calc
      _ ≤ 2 * (∫ x in radiusTwoOpens, χ.1 x ^ 2 * ‖TauCeti.W1p.gradient u x‖ ^ 2
          ∂(volume : Measure R3)) + 2 * (∫ x in radiusTwoOpens, ‖gradient χ.1 x‖ ^ 2 *
          TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3)) :=
        TauCeti.W1p.norm_gradient_contDiffSMul_sq_le χ.2 hM
          (fun x _ => hAbs x) (fun x _ => hGrad x) u
      _ ≤ 2 * ((2 * Lam / lam) ^ 2 * (∫ x in radiusTwoOpens, ‖gradient χ.1 x‖ ^ 2 *
          TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3))) +
          2 * (∫ x in radiusTwoOpens, ‖gradient χ.1 x‖ ^ 2 * TauCeti.W1p.value u x ^ 2
          ∂(volume : Measure R3)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hEnergy f χ.1 χ.2 hCompact hAnn) (by norm_num)) le_rfl
      _ = (2 * (2 * Lam / lam) ^ 2 + 2) * (∫ x in radiusTwoOpens, ‖gradient χ.1 x‖ ^ 2 *
          TauCeti.W1p.value u x ^ 2 ∂(volume : Measure R3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWeighted (by positivity)
  refine ⟨TauCeti.W1p.contDiffSMul_mem_w1p0Submodule χ.2 hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) (radiusTwoSourceSolution g hg f).property, ?_⟩
  calc
    ‖w‖ ^ 2 = ‖TauCeti.W1p.value w‖ ^ 2 + ‖TauCeti.W1p.gradient w‖ ^ 2 :=
      TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq w
    _ ≤ M ^ 2 * I + (2 * (2 * Lam / lam) ^ 2 + 2) * (M ^ 2 * I) := add_le_add hValue hGradient
    _ = M ^ 2 * c * I := by dsimp only [c]; ring

theorem exists_radiusTwoSource_localized_poleCutoff_limit_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (χ : SmoothData), HasCompactSupport χ.1 →
      ∀ (S : Set R3), MeasurableSet S → tsupport χ.1 ⊆ S →
      ∀ (M : ℝ) (hM : 0 ≤ M), (∀ x : R3, |χ.1 x| ≤ M) →
      (∀ x : R3, ‖gradient χ.1 x‖ ≤ M) →
      ∀ (ρ : ℕ → RadiusTwoL2) (K : RadiusTwoL2),
      (∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3).restrict radiusTwoOpens,
        χ.1 x * ρ n x = 0) →
      Tendsto (fun n => TauCeti.W1p.value (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1))
        atTop (𝓝 K) →
      ∃ w : RadiusTwoH1Zero,
        ((TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun x => χ.1 x * K x)) ∧
        ‖(w : RadiusTwoH1)‖ ^ 2 ≤ M ^ 2 * c *
          ∫ x in (radiusTwoOpens : Set R3) ∩ S, K x ^ 2 ∂(volume : Measure R3) := by
  obtain ⟨c, hc, hGraph⟩ := exists_radiusTwoSource_localized_poleCutoff_graph_bound g hg
  refine ⟨c, hc, ?_⟩
  intro χ hCompact S hS hSupp M hM hAbs hGrad ρ K hAnn hLimit
  let T : RadiusTwoH1 →L[ℝ] RadiusTwoH1 := TauCeti.W1p.contDiffSMulL χ.1 χ.2 hM
    (fun x _ => hAbs x) (fun x _ => hGrad x)
  let u (n : ℕ) : RadiusTwoH1 := (radiusTwoSourceSolution g hg (ρ n) : RadiusTwoH1)
  obtain ⟨w, hw⟩ := exists_radiusTwoSource_poleCutoff_zero_limit g hg χ.1 χ.2 hCompact
    M hM hAbs hGrad ρ hAnn hLimit.cauchySeq
  have hValue := value_radiusTwoCutoff_limit_eq_mul χ hM
    (fun x _ => hAbs x) (fun x _ => hGrad x) u (w : RadiusTwoH1) K hLimit hw
  let R : RadiusTwoL2 →L[ℝ]
      Lp ℝ 2 (((volume : Measure R3).restrict radiusTwoOpens).restrict S) :=
    MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ ((volume : Measure R3).restrict radiusTwoOpens) 2 S
  have hRestrictNorm (v : RadiusTwoL2) : ‖R v‖ ^ 2 =
      ∫ x in (radiusTwoOpens : Set R3) ∩ S, v x ^ 2 ∂(volume : Measure R3) := by
    calc
      ‖R v‖ ^ 2 = ∫ x, ‖R v x‖ ^ 2
          ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S) :=
        (Lp.integral_norm_sq_eq_norm_sq (R v)).symm
      _ = ∫ x, ‖v x‖ ^ 2 ∂(((volume : Measure R3).restrict radiusTwoOpens).restrict S) := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.LpToLpRestrictCLM_coeFn ℝ S v] with x hx
        rw [hx]
      _ = _ := by
        rw [Measure.restrict_restrict hS]
        simp only [Real.norm_eq_abs, sq_abs, Set.inter_comm]
  have hLeft : Tendsto (fun n => ‖T (u n)‖ ^ 2) atTop (𝓝 (‖(w : RadiusTwoH1)‖ ^ 2)) :=
    hw.norm.pow 2
  have hRight : Tendsto (fun n => M ^ 2 * c * ‖R (TauCeti.W1p.value (u n))‖ ^ 2)
      atTop (𝓝 (M ^ 2 * c * ‖R K‖ ^ 2)) :=
    (((R.continuous.tendsto K).comp hLimit).norm.pow 2).const_mul (M ^ 2 * c)
  have hInequality : ∀ᶠ n in atTop,
      ‖T (u n)‖ ^ 2 ≤ M ^ 2 * c * ‖R (TauCeti.W1p.value (u n))‖ ^ 2 := by
    filter_upwards [hAnn] with n hn
    have h := (hGraph χ hCompact S hS hSupp M hM hAbs hGrad (ρ n) hn).2
    rw [hRestrictNorm]
    exact h
  refine ⟨w, hValue, ?_⟩
  have hNorm := le_of_tendsto_of_tendsto hLeft hRight hInequality
  rw [hRestrictNorm] at hNorm
  exact hNorm

theorem exists_radiusTwo_finiteRow_localized_cutoff_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (χ : SmoothData), HasCompactSupport χ.1 →
      ∀ (S : Set R3), MeasurableSet S → tsupport χ.1 ⊆ S →
      ∀ (M : ℝ) (hM : 0 ≤ M), (∀ x : R3, |χ.1 x| ≤ M) →
      (∀ x : R3, ‖gradient χ.1 x‖ ≤ M) →
      ∀ (m : ℕ) (a : Fin m → ℝ) (p : Fin m → (radiusTwoOpens : Set R3)),
      (∀ i, (p i : R3) ∉ tsupport χ.1) →
      ∃ w : RadiusTwoH1Zero,
        ((TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
            (fun x => χ.1 x * (∑ i : Fin m, a i • K (p i)) x)) ∧
        ((TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
            (fun x => χ.1 x * ∑ i : Fin m, a i * G (p i) x)) ∧
        ‖(w : RadiusTwoH1)‖ ^ 2 ≤ M ^ 2 * c *
          ∫ x in (radiusTwoOpens : Set R3) ∩ S,
            ((∑ i : Fin m, a i • K (p i)) x) ^ 2 ∂(volume : Measure R3) := by
  classical
  obtain ⟨c, hc, hLimitBound⟩ := exists_radiusTwoSource_localized_poleCutoff_limit_bound g hg
  refine ⟨c, hc, ?_⟩
  intro χ hCompact S hS hSupp M hM hAbs hGrad m a p hPole
  let ψ (i : Fin m) (n : ℕ) : 𝓓(radiusTwoOpens, ℝ) :=
    radiusTwoCommonNormalizedDeltaSequence (radiusTwoCanonicalRoom (p i))
      (radiusTwoCanonicalRoom_pos (p i)) (radiusTwoCanonicalRoom_lt_one (p i))
      (radiusTwoCanonicalNormalizedPole (p i)) (radiusTwoCanonicalNormalizedPole_mem_room (p i)) n
  let ρ (i : Fin m) (n : ℕ) : RadiusTwoL2 := smoothRadiusTwoForcing ⟨ψ i n, (ψ i n).contDiff⟩
  let f (n : ℕ) : RadiusTwoL2 := ∑ i : Fin m, a i • ρ i n
  let A : RadiusTwoL2 →L[ℝ] RadiusTwoL2 :=
    (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := radiusTwoOpens) (p := 2)).comp
      (radiusTwoSourceSolutionL g hg)
  have hA (v : RadiusTwoL2) : A v =
      TauCeti.W1p.value (radiusTwoSourceSolution g hg v : RadiusTwoH1) := rfl
  have hSingle (i : Fin m) : Tendsto (fun n => A (ρ i n)) atTop (𝓝 (K (p i))) :=
    (hData.1 (p i)).1
  have hFinite : Tendsto (fun n => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (f n) : RadiusTwoH1)) atTop (𝓝 (∑ i : Fin m, a i • K (p i))) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin m))
      (fun i _ => (hSingle i).const_smul (a i))
    change Tendsto (fun n => A (f n)) atTop (𝓝 (∑ i : Fin m, a i • K (p i)))
    simpa only [f, map_sum, map_smul] using h
  have hAnnSingle (i : Fin m) : ∀ᶠ n in atTop,
      ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens, χ.1 z * ρ i n z = 0 := by
    let q : R3 := radiusTwoCanonicalNormalizedPole (p i)
    have hZero : χ.1 =ᶠ[𝓝 ((2 : ℝ) • q)] (0 : R3 → ℝ) := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      simpa only [q, two_smul_radiusTwoCanonicalNormalizedPole] using hPole i
    have hNear : ∀ᶠ y in 𝓝 q, χ.1 ((2 : ℝ) • y) = 0 :=
      hZero.comp_tendsto ((continuous_const_smul (2 : ℝ)).tendsto q)
    obtain ⟨δ, hδ, hδZero⟩ := Metric.mem_nhds_iff.mp hNear
    have heps : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)
    have hSmall : ∀ᶠ n in atTop, (1/2 : ℝ)^n < δ := (tendsto_order.1 heps).2 _ hδ
    filter_upwards [hSmall] with n hn
    filter_upwards [smoothRadiusTwoForcing_ae ⟨ψ i n, (ψ i n).contDiff⟩] with z hz
    change χ.1 z * smoothRadiusTwoForcing ⟨ψ i n, (ψ i n).contDiff⟩ z = 0
    by_cases hzψ : ψ i n z = 0
    · rw [hz, hzψ, mul_zero]
    · have hDist := ((radiusTwoCommonNormalizedDeltaSequence_properties
          (radiusTwoCanonicalRoom (p i)) (radiusTwoCanonicalRoom_pos (p i))
          (radiusTwoCanonicalRoom_lt_one (p i)) (radiusTwoCanonicalNormalizedPole (p i))
          (radiusTwoCanonicalNormalizedPole_mem_room (p i)) n).2.2 z (subset_tsupport _ hzψ)).2
      have hχ := hδZero (show (1/2 : ℝ) • z ∈ ball q δ from hDist.trans_lt hn)
      have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by rw [smul_smul]; norm_num
      change χ.1 ((2 : ℝ) • ((1/2 : ℝ) • z)) = 0 at hχ
      rw [hCancel] at hχ
      rw [hχ, zero_mul]
  have hAnn : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
      χ.1 z * f n z = 0 := by
    filter_upwards [Filter.eventually_all.mpr hAnnSingle] with n hn
    have hAE (i : Fin m) : ((a i • ρ i n : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => a i * ρ i n z) := by
      filter_upwards [Lp.coeFn_smul (a i) (ρ i n)] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz
    have hSum : (f n : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => ∑ i : Fin m, a i * ρ i n z) := by
      have hSumRaw := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin m))
        (fun i => a i • ρ i n)
      filter_upwards [hSumRaw, ae_all_iff.mpr hAE] with z hz hzi
      exact hz.trans (Finset.sum_congr rfl (fun i _ => hzi i))
    filter_upwards [hSum, ae_all_iff.mpr hn] with z hz hzero
    rw [hz, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    calc
      χ.1 z * (a i * ρ i n z) = a i * (χ.1 z * ρ i n z) := by ring
      _ = 0 := by rw [hzero i, mul_zero]
  obtain ⟨w, hValue, hNorm⟩ := hLimitBound χ hCompact S hS hSupp M hM hAbs hGrad
    f (∑ i : Fin m, a i • K (p i)) hAnn hFinite
  have hKG : ((∑ i : Fin m, a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => ∑ i : Fin m, a i * G (p i) z) := by
    have hi (i : Fin m) : ((a i • K (p i) : RadiusTwoL2) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => a i * G (p i) z) := by
      filter_upwards [Lp.coeFn_smul (a i) (K (p i)), (hData.1 (p i)).2.2.1] with z hz hg
      simpa only [Pi.smul_apply, smul_eq_mul, hg] using hz
    have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin m))
      (fun i => a i • K (p i))
    filter_upwards [hSum, ae_all_iff.mpr hi] with z hz hzi
    exact hz.trans (Finset.sum_congr rfl (fun i _ => hzi i))
  have hCutKG : (fun z => χ.1 z * (∑ i : Fin m, a i • K (p i) : RadiusTwoL2) z)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens]
        (fun z => χ.1 z * ∑ i : Fin m, a i * G (p i) z) := by
    filter_upwards [hKG] with z hz
    exact congrArg (fun t : ℝ => χ.1 z * t) hz
  exact ⟨w, hValue, hValue.trans hCutKG, hNorm⟩

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSource_localized_poleCutoff_graph_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSource_localized_poleCutoff_limit_bound
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_finiteRow_localized_cutoff_bound
