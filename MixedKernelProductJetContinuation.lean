import MixedKernelMonotoneCurrentPair
import MixedKernelPositiveChartAgreement
import MixedKernelObservedOutputRooms
import MixedKernelCurrentCommonPair
import MixedKernelProductOpenUCP
import MixedKernelCenteredRooms
import MixedKernelFiniteInterpolation
import MixedKernelKnownSideNearOne
import MixedKernelAnnulusGeometry
import MixedKernelKnownSideCompactBuffer
import MixedKernelActualSeparatorAnchors
import MixedKernelKnownSideNeighborhood
import MixedKernelCompatibleGluing
import MixedKernelFullCrossAssembly
import MixedKernelFactorJetContinuation
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

section ProductTermJets

/-- SL-6a: composing with a continuous linear map of norm `≤ 1` (here `fst`/`snd`) does not
increase any jet, on the open preimage of an open set (within-derivatives converted exactly). -/
theorem norm_iteratedFDeriv_comp_clm_le (O : Set R3) (hO : IsOpen O) (W : R3 → ℝ)
    (hW : ContDiffOn ℝ ∞ W O) (Lm : R3 × R3 →L[ℝ] R3) (hL : ‖Lm‖ ≤ 1)
    (z : R3 × R3) (hz : Lm z ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (W ∘ Lm) z‖ ≤ ‖iteratedFDeriv ℝ k W (Lm z)‖ := by
  have hpre : IsOpen (Lm ⁻¹' O) := hO.preimage Lm.continuous
  have h := Lm.iteratedFDerivWithin_comp_right hW hO.uniqueDiffOn hpre.uniqueDiffOn hz
    (i := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hpre hz, iteratedFDerivWithin_of_isOpen k hO hz] at h
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

/-- SL-6b: Leibniz bound for the product term `z ↦ W z.1 * b z.2` on the open box `O1 ×ˢ O2`
(pinned `norm_iteratedFDerivWithin_mul_le`, open-set within/global conversion). -/
theorem productTerm_jet_bound (O1 O2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    (W b : R3 → ℝ) (hW : ContDiffOn ℝ ∞ W O1) (hb : ContDiffOn ℝ ∞ b O2) (n : ℕ)
    (c1 c2 : ℕ → ℝ) (z : R3 × R3) (hz1 : z.1 ∈ O1) (hz2 : z.2 ∈ O2)
    (h1 : ∀ k ≤ n, ‖iteratedFDeriv ℝ k W z.1‖ ≤ c1 k)
    (h2 : ∀ k ≤ n, ‖iteratedFDeriv ℝ k b z.2‖ ≤ c2 k) :
    ‖iteratedFDeriv ℝ n (fun z : R3 × R3 => W z.1 * b z.2) z‖ ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * c1 k * c2 (n - k) := by
  have hs : IsOpen (O1 ×ˢ O2) := hO1.prod hO2
  have hzs : z ∈ O1 ×ˢ O2 := ⟨hz1, hz2⟩
  have hf : ContDiffOn ℝ ∞ (W ∘ ContinuousLinearMap.fst ℝ R3 R3) (O1 ×ˢ O2) :=
    (hW.comp_continuousLinearMap (ContinuousLinearMap.fst ℝ R3 R3)).mono fun x hx => hx.1
  have hg : ContDiffOn ℝ ∞ (b ∘ ContinuousLinearMap.snd ℝ R3 R3) (O1 ×ˢ O2) :=
    (hb.comp_continuousLinearMap (ContinuousLinearMap.snd ℝ R3 R3)).mono fun x hx => hx.2
  have hmul := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hzs (n := n)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hs hzs] at hmul
  refine hmul.trans (Finset.sum_le_sum fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [iteratedFDerivWithin_of_isOpen k hs hzs, iteratedFDerivWithin_of_isOpen (n - k) hs hzs]
  have hA := (norm_iteratedFDeriv_comp_clm_le O1 hO1 W hW (ContinuousLinearMap.fst ℝ R3 R3)
    (ContinuousLinearMap.norm_fst_le ..) z hz1 k).trans (h1 k hkn)
  have hB := (norm_iteratedFDeriv_comp_clm_le O2 hO2 b hb (ContinuousLinearMap.snd ℝ R3 R3)
    (ContinuousLinearMap.norm_snd_le ..) z hz2 (n - k)).trans (h2 (n - k) (Nat.sub_le n k))
  have hc1 : 0 ≤ c1 k := (norm_nonneg _).trans hA
  exact mul_le_mul (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)) hB (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hc1)

/-- SL-6c: for ANY families of factors with compact jet bounds `C1 k * a i` on `K ⊆ O1` and
`C2 k * c i` on `J ⊆ O2` (constants chosen BEFORE the index), every order-`n` jet of each
product term on `K ×ˢ J` is bounded by ONE constant times `a i * c i`, independent of `i`. -/
theorem productFamily_jet_bound (O1 O2 K J : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2) {ι : Type*} (W b : ι → R3 → ℝ)
    (hWs : ∀ i, ContDiffOn ℝ ∞ (W i) O1) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) O2)
    (a c : ι → ℝ) (C1 C2 : ℕ → ℝ)
    (hW : ∀ i k, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (W i) x‖ ≤ C1 k * a i)
    (hb : ∀ i k, ∀ y ∈ J, ‖iteratedFDeriv ℝ k (b i) y‖ ≤ C2 k * c i) (n : ℕ) :
    ∀ i, ∀ z ∈ K ×ˢ J,
      ‖iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z‖ ≤
        (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C1 k * C2 (n - k)) * (a i * c i) := by
  intro i z hz
  refine (productTerm_jet_bound O1 O2 hO1 hO2 (W i) (b i) (hWs i) (hbs i) n
    (fun k => C1 k * a i) (fun k => C2 k * c i) z (hKO1 hz.1) (hJO2 hz.2)
    (fun k _ => hW i k z.1 hz.1) (fun k _ => hb i k z.2 hz.2)).trans_eq ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- SL-6d: the norm products of the SAME arm bounds are summable (exponent `γ₁+γ₂-1 > 0`). -/
theorem summable_norm_products {ι : Type*} (a c μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (ha0 : ∀ i, 0 ≤ a i) (hc0 : ∀ i, 0 ≤ c i) {K1 K2 γ1 γ2 : ℝ}
    (ha : ∀ i, a i ≤ K1 * μ i ^ γ1) (hc : ∀ i, c i ≤ K2 * μ i ^ (γ2 - 1))
    (hγ : 0 < γ1 + γ2 - 1) (hsum : ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β) :
    Summable fun i => a i * c i := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (hc0 i)) (fun i => ?_)
    ((hsum _ hγ).mul_left (K1 * K2))
  calc a i * c i ≤ (K1 * μ i ^ γ1) * (K2 * μ i ^ (γ2 - 1)) :=
        mul_le_mul (ha i) (hc i) (hc0 i) ((ha0 i).trans (ha i))
    _ = K1 * K2 * μ i ^ (γ1 + γ2 - 1) := by
        rw [show γ1 + γ2 - 1 = γ1 + (γ2 - 1) by ring, Real.rpow_add (hμ i)]
        ring

open MeasureTheory in
/-- SL-5b: the literal normalized second equation on `D2 ⊇ O2` is the divergence equation of the
SAME dilated second principal coefficient, so SL-5a bounds every jet of `b` on compact `J ⊆ O2`
by `C ‖g‖` for its `L²(O2)` class `g`, `C` chosen BEFORE `b`. -/
theorem secondFactor_jet_bound (S : KnownSideSourceData) (L lam : ℝ) (D2 O2 : Set R3)
    (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2) (J : Set R3) (hJ : IsCompact J) (hJO2 : J ⊆ O2)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : R3 → ℝ, ContDiffOn ℝ ∞ b D2 →
      (∀ y ∈ D2, normalizedSecondLaplacian S.g1 S.g2 L lam b y = 0) →
      ∀ g : Lp ℝ 2 ((volume : Measure R3).restrict O2),
        b =ᵐ[(volume : Measure R3).restrict O2] (g : R3 → ℝ) →
        ∀ y ∈ J, ‖iteratedFDeriv ℝ n b y‖ ≤ C * ‖g‖ := by
  have hdil : ContDiff ℝ ∞ (fun x : R3 => lam • x) :=
    (lam • ContinuousLinearMap.id ℝ R3).contDiff
  have hA : ContDiff ℝ ∞ (fun y : R3 => principalCoefficient S.g2 (lam • y)) :=
    (contDiff_principalCoefficient S.g2 S.g2_admissible).comp hdil
  obtain ⟨C, hC, hbound⟩ := smoothSolution_jet_bound O2 hO2
    (fun y => principalCoefficient S.g2 (lam • y)) hA.contDiffOn
    (fun y _ => principalCoefficient_posDef S.g2 S.g2_admissible (lam • y)) J hJ hJO2 n
  refine ⟨C, hC, fun b hb hP g hg y hy => hbound b (hb.mono hO2D2) (fun x hx => ?_) g hg y hy⟩
  exact (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible
    L lam b x).mp (hP x (hO2D2 hx))

open MeasureTheory in
/-- SL-6e: the ACTUAL series on ONE common pair. For the SAME family `(ι, w, μ)` with
`CrossSeriesOn`, the SAME classes `gᵢ = [bᵢ]_{O2}` give summable `‖R_{O1}wᵢ‖ ‖gᵢ‖`, and on every
compact `K ×ˢ J ⊆ O1 ×ˢ O2`, for every order `n`, ONE constant `B` bounds the order-`n` jet of
every actual term `z ↦ Wᵢ(z.1) bᵢ(z.2)` (smooth representative `Wᵢ` of `R_{O1}wᵢ`, actual
unnormalized `bᵢ`) by `B ‖R_{O1}wᵢ‖ ‖gᵢ‖`. -/
theorem actualTerm_jet_bound (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1) (T : Set R3)
    (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J) (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2) :
    ∃ g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2),
      (∀ i, actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      Summable (fun i => ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ * ‖g i‖) ∧
      ∀ n : ℕ, ∃ B : ℝ, ∀ i, ∀ z ∈ K ×ˢ J,
        ‖iteratedFDeriv ℝ n (fun z : R3 × R3 =>
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z‖ ≤
          B * (‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ * ‖g i‖) := by
  obtain ⟨⟨hμ, -, -⟩, -, hsum, M, -, harms, g, hgae, hg, hf, hγ, -⟩ := h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  refine ⟨g, hgae, summable_norm_products _ _ μ hμ (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hf hg hγ hsum, fun n => ?_⟩
  choose C1 _hC1 hW1 using fun k => H1.2 K hK hKO1 k
  choose C2 _hC2 hb2 using fun k => secondFactor_jet_bound S L lam D2 O2 hO2 hO2D2 J hJ hJO2 k
  exact ⟨_, productFamily_jet_bound O1 O2 K J hO1 hO2 hKO1 hJO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (harms i).1.mono hO2D2)
    (fun i => ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖) (fun i => ‖g i‖) C1 C2
    (fun i k x hx => hW1 k (w i) x hx)
    (fun i k y hy => hb2 k _ (harms i).1 (harms i).2.1 (g i) (hgae i) y hy) n⟩

/-- SL-7a: normal convergence of one jet order. If every order-`n` jet of the product terms is
bounded on `K ×ˢ J` by a summable `u`, then along ANY cofinal finset sequence `t` the order-`n`
jets of the SAME partial sums converge uniformly on `K ×ˢ J` to the `tsum` of the term jets
(jet of a finite sum = sum of jets at interior points of the open box). -/
theorem series_jet_tendstoUniformlyOn (O1 O2 K J : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2) {ι : Type*} (W b : ι → R3 → ℝ)
    (hWs : ∀ i, ContDiffOn ℝ ∞ (W i) O1) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) O2)
    (u : ι → ℝ) (hu : Summable u) (n : ℕ)
    (hB : ∀ i, ∀ z ∈ K ×ˢ J,
      ‖iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z‖ ≤ u i)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    TendstoUniformlyOn
      (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) z)
      (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
      atTop (K ×ˢ J) := by
  have hterm : ∀ i, ContDiffOn ℝ ∞ (fun z : R3 × R3 => W i z.1 * b i z.2) (O1 ×ˢ O2) := by
    intro i
    have hf : ContDiffOn ℝ ∞ (W i ∘ ContinuousLinearMap.fst ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hWs i).comp_continuousLinearMap (ContinuousLinearMap.fst ℝ R3 R3)).mono fun x hx => hx.1
    have hg : ContDiffOn ℝ ∞ (b i ∘ ContinuousLinearMap.snd ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hbs i).comp_continuousLinearMap (ContinuousLinearMap.snd ℝ R3 R3)).mono fun x hx => hx.2
    exact hf.mul hg
  haveI : CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin n => R3 × R3) ℝ) :=
    ContinuousMultilinearMap.instCompleteSpace
  have hT : TendstoUniformlyOn
      (fun k z => ∑ i ∈ t k, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
      (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
      atTop (K ×ˢ J) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    exact ht.eventually (Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_tsum hu fun i z hz => hB i z hz) ε hε)
  refine hT.congr (Eventually.of_forall fun k z hz => ?_)
  have hz' : z ∈ O1 ×ˢ O2 := ⟨hKO1 hz.1, hJO2 hz.2⟩
  have hc : ∀ i ∈ t k, ContDiffAt ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z := fun i _ =>
    ((hterm i).contDiffAt ((hO1.prod hO2).mem_nhds hz')).of_le (by exact_mod_cast le_top)
  have h := iteratedFDeriv_sum_apply hc
  rw [Finset.sum_fn] at h
  exact h.symm

open MeasureTheory in
/-- SL-7b: the ACTUAL series. Along ANY cofinal finset sequence `t` of the SAME indices (e.g. the
one of `crossSeries_actual_limit`), for every compact `K ×ˢ J ⊆ O1 ×ˢ O2` and EVERY order `n`, the
order-`n` jets of the SAME partial sums `∑_{i ∈ t k} Wᵢ(z.1) bᵢ(z.2)` (actual unnormalized `bᵢ`)
converge uniformly on `K ×ˢ J` to the `tsum` of the term jets. -/
theorem actualSeries_jet_tendstoUniformlyOn (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J) (hKO1 : K ⊆ O1) (hJO2 : J ⊆ O2)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) (n : ℕ) :
    TendstoUniformlyOn
      (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z)
      (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 =>
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z)
      atTop (K ×ˢ J) := by
  obtain ⟨g, -, hsumm, hB⟩ := actualTerm_jet_bound S L lam D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2
    hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2
  obtain ⟨-, -, -, M, -, harms, -⟩ := h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  obtain ⟨B, hBn⟩ := hB n
  exact series_jet_tendstoUniformlyOn O1 O2 K J hO1 hO2 hKO1 hJO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (harms i).1.mono hO2D2) _ (hsumm.mul_left B) n hBn t ht

/-- SL-8a: open-set all-jet uniform limit ⇒ C^∞ (exact adaptation of the checked
FiniteHarmonicProductL2Limit block 504–553, with the ball specialization removed): if smooth
`Hs j` on open `O` have every jet converging uniformly on `O` to `G m`, then
`H = (G 0 ·).curry0` is C^∞ on `O` and its jets are `G m`. -/
theorem contDiffOn_of_jet_tendstoUniformlyOn (O : Set (R3 × R3)) (hO : IsOpen O)
    (Hs : ℕ → R3 × R3 → ℝ) (hHs : ∀ j, ContDiffOn ℝ ∞ (Hs j) O)
    (G : (m : ℕ) → R3 × R3 → ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)
    (hT : ∀ m, TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (Hs j)) (G m) atTop O) :
    ContDiffOn ℝ ∞ (fun p => (G 0 p).curry0) O ∧
      ∀ m, ∀ p ∈ O, G m p = iteratedFDeriv ℝ m (fun p => (G 0 p).curry0) p := by
  have hCont (m : ℕ) : ContinuousOn (G m) O := by
    apply (hT m).continuousOn
    apply (Eventually.of_forall (f := atTop) (fun j => ?_)).frequently
    have hc := (hHs j).continuousOn_iteratedFDerivWithin (m := m) (by simp) hO.uniqueDiffOn
    exact hc.congr (fun p hp => (iteratedFDerivWithin_of_isOpen m hO hp).symm)
  have hCurry (m : ℕ) : TendstoUniformlyOn
      (fun j p => (iteratedFDeriv ℝ (m + 1) (Hs j) p).curryLeft)
      (fun p => (G (m + 1) p).curryLeft) atTop O := by
    let C : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →L[ℝ]
        ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    have hFun : (C : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
        ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) =
        fun L => L.curryLeft := rfl
    have hUC : UniformContinuous (fun L :
        ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ => L.curryLeft) := by
      let A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →+
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ) :=
        C.toLinearMap.toAddMonoidHom
      have hA : Continuous (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) :=
        C.continuous
      have hAU : UniformContinuous (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) :=
        uniformContinuous_addMonoidHom_of_continuous hA
      have hAFun : (A : ContinuousMultilinearMap ℝ (fun _ : Fin (m+1) => R3 × R3) ℝ →
          ((R3 × R3) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => R3 × R3) ℝ)) =
          fun L => L.curryLeft := hFun
      exact hAFun ▸ hAU
    intro E hE
    exact (hT (m+1)) _ (hUC hE)
  let H : R3 × R3 → ℝ := fun p => (G 0 p).curry0
  let series : R3 × R3 → FormalMultilinearSeries ℝ (R3 × R3) ℝ := fun p m => G m p
  have hTaylor (k : ℕ) : HasFTaylorSeriesUpToOn (k : ℕ∞) H series O := by
    refine ⟨fun p _ => rfl, ?_, ?_⟩
    · intro m hm p hp
      have hm' : m < k := by exact_mod_cast hm
      apply (hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hO
        (f := fun j => iteratedFDeriv ℝ m (Hs j))
        (f' := fun j p => (iteratedFDeriv ℝ (m + 1) (Hs j) p).curryLeft)
        (hCurry m) (fun j q hq => ?_) (fun q hq => (hT m).tendsto_at hq) hp).hasFDerivWithinAt
      have hd := ((hHs j).contDiffAt (hO.mem_nhds hq)).differentiableAt_iteratedFDeriv
        (m := m) (by exact_mod_cast (WithTop.coe_lt_top m))
      convert! hd.hasFDerivAt using 1 <;> rfl
    · intro m hm
      exact hCont m
  have hH : ContDiffOn ℝ ∞ H O := contDiffOn_infty.mpr (fun k => (hTaylor k).contDiffOn)
  refine ⟨hH, fun m p hp => ?_⟩
  exact ((hTaylor m).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hO.uniqueDiffOn hp).trans
    (iteratedFDerivWithin_of_isOpen m hO hp)

/-- SL-8b: local-to-global. If on EVERY compact `K ×ˢ J ⊆ O1 ×ˢ O2` every jet of the SAME
partial sums along `t` converges uniformly to the `tsum` of term jets (SL-7b's conclusion), then
the ONE global limit `z ↦ (∑' i, D⁰ termᵢ z).curry0` is C^∞ on the whole open `O1 ×ˢ O2`
(SL-8a on open ball boxes with compact closed-ball closures, then `contDiffOn_of_locally`). -/
theorem series_contDiffOn_of_local_jets (O1 O2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    {ι : Type*} (W b : ι → R3 → ℝ)
    (hWs : ∀ i, ContDiffOn ℝ ∞ (W i) O1) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) O2)
    (t : ℕ → Finset ι)
    (hjets : ∀ K J : Set R3, IsCompact K → IsCompact J → K ⊆ O1 → J ⊆ O2 → ∀ n : ℕ,
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) z)
        (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
        atTop (K ×ˢ J)) :
    ContDiffOn ℝ ∞
      (fun z => (∑' i, iteratedFDeriv ℝ 0 (fun z : R3 × R3 => W i z.1 * b i z.2) z).curry0)
      (O1 ×ˢ O2) := by
  have hterm : ∀ i, ContDiffOn ℝ ∞ (fun z : R3 × R3 => W i z.1 * b i z.2) (O1 ×ˢ O2) := by
    intro i
    have hf : ContDiffOn ℝ ∞ (W i ∘ ContinuousLinearMap.fst ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hWs i).comp_continuousLinearMap (ContinuousLinearMap.fst ℝ R3 R3)).mono fun x hx => hx.1
    have hg : ContDiffOn ℝ ∞ (b i ∘ ContinuousLinearMap.snd ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hbs i).comp_continuousLinearMap (ContinuousLinearMap.snd ℝ R3 R3)).mono fun x hx => hx.2
    exact hf.mul hg
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  obtain ⟨r1, hr1, h1⟩ := Metric.isOpen_iff.mp hO1 z.1 hz.1
  obtain ⟨r2, hr2, h2⟩ := Metric.isOpen_iff.mp hO2 z.2 hz.2
  have hK : closedBall z.1 (r1 / 2) ⊆ O1 := (closedBall_subset_ball (half_lt_self hr1)).trans h1
  have hJ : closedBall z.2 (r2 / 2) ⊆ O2 := (closedBall_subset_ball (half_lt_self hr2)).trans h2
  have hU : IsOpen (ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2)) := isOpen_ball.prod isOpen_ball
  have hUKJ : ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2) ⊆
      closedBall z.1 (r1 / 2) ×ˢ closedBall z.2 (r2 / 2) :=
    prod_mono ball_subset_closedBall ball_subset_closedBall
  have hUO : ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2) ⊆ O1 ×ˢ O2 := hUKJ.trans (prod_mono hK hJ)
  have hHs : ∀ k, ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2)
      (ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2)) := fun k =>
    (ContDiffOn.sum fun i _ => hterm i).mono hUO
  obtain ⟨hH, -⟩ := contDiffOn_of_jet_tendstoUniformlyOn _ hU
    (fun k z => ∑ i ∈ t k, W i z.1 * b i z.2) hHs
    (fun m z => ∑' i, iteratedFDeriv ℝ m (fun z : R3 × R3 => W i z.1 * b i z.2) z)
    (fun m => (hjets _ _ (isCompact_closedBall _ _) (isCompact_closedBall _ _) hK hJ m).mono hUKJ)
  exact ⟨_, hU, ⟨mem_ball_self (half_pos hr1), mem_ball_self (half_pos hr2)⟩,
    hH.mono inter_subset_right⟩

open MeasureTheory in
/-- SL-8c: the ACTUAL limit of the SAME series along ANY cofinal `t` (e.g. that of
`crossSeries_actual_limit`), with actual `Wᵢ` and unnormalized `bᵢ`, is C^∞ on all of `O1 ×ˢ O2`. -/
theorem actualSeries_contDiffOn (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ContDiffOn ℝ ∞ (fun z => (∑' i, iteratedFDeriv ℝ 0 (fun z : R3 × R3 =>
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z).curry0) (O1 ×ˢ O2) := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) D2 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => (harms i).1
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  exact series_contDiffOn_of_local_jets O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => actualSeries_jet_tendstoUniformlyOn S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)

/-- SL-8d: `curry0` of the `tsum` of order-0 jets is the `tsum` of the values. Only `T2Space ℝ`
is used (summable case via `ContinuousLinearMap.map_tsum` into `ℝ`; otherwise both sums vanish). -/
theorem curry0_tsum_iteratedFDeriv_zero {ι : Type*} (f : ι → R3 × R3 → ℝ) (z : R3 × R3) :
    (∑' i, iteratedFDeriv ℝ 0 (f i) z).curry0 = ∑' i, f i z := by
  let e : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => R3 × R3) ℝ ≃L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ (R3 × R3) ℝ).toContinuousLinearEquiv
  have hc : ∀ L : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => R3 × R3) ℝ, L.curry0 = e L :=
    fun L => rfl
  have hiff : Summable (fun i => iteratedFDeriv ℝ 0 (f i) z) ↔ Summable (fun i => f i z) :=
    e.symm.summable (f := fun i => f i z)
  rw [hc]
  by_cases hs : Summable (fun i => f i z)
  · exact (e : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => R3 × R3) ℝ →L[ℝ] ℝ).map_tsum
      (hiff.2 hs)
  · rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable (mt hiff.1 hs), map_zero]

/-- SL-8e: the ONE limit `z ↦ ∑' Wᵢ(z.1) bᵢ(z.2)` of the SAME partial sums is C^∞ on `O1 ×ˢ O2`,
and each of its jets at every point is the `tsum` of the term jets (SL-8a second conclusion on
the SL-8b ball boxes, rewritten by SL-8d). -/
theorem series_limit_contDiffOn_and_jets (O1 O2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    {ι : Type*} (W b : ι → R3 → ℝ)
    (hWs : ∀ i, ContDiffOn ℝ ∞ (W i) O1) (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) O2)
    (t : ℕ → Finset ι)
    (hjets : ∀ K J : Set R3, IsCompact K → IsCompact J → K ⊆ O1 → J ⊆ O2 → ∀ n : ℕ,
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) z)
        (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
        atTop (K ×ˢ J)) :
    ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑' i, W i z.1 * b i z.2) (O1 ×ˢ O2) ∧
      ∀ m : ℕ, ∀ z ∈ O1 ×ˢ O2,
        iteratedFDeriv ℝ m (fun z : R3 × R3 => ∑' i, W i z.1 * b i z.2) z =
          ∑' i, iteratedFDeriv ℝ m (fun z : R3 × R3 => W i z.1 * b i z.2) z := by
  have hH : (fun z => (∑' i, iteratedFDeriv ℝ 0
      (fun z : R3 × R3 => W i z.1 * b i z.2) z).curry0) =
      fun z : R3 × R3 => ∑' i, W i z.1 * b i z.2 :=
    funext fun z => curry0_tsum_iteratedFDeriv_zero (fun i (z : R3 × R3) => W i z.1 * b i z.2) z
  have h8 := series_contDiffOn_of_local_jets O1 O2 hO1 hO2 W b hWs hbs t hjets
  rw [hH] at h8
  refine ⟨h8, fun m z hz => ?_⟩
  have hterm : ∀ i, ContDiffOn ℝ ∞ (fun z : R3 × R3 => W i z.1 * b i z.2) (O1 ×ˢ O2) := by
    intro i
    have hf : ContDiffOn ℝ ∞ (W i ∘ ContinuousLinearMap.fst ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hWs i).comp_continuousLinearMap (ContinuousLinearMap.fst ℝ R3 R3)).mono fun x hx => hx.1
    have hg : ContDiffOn ℝ ∞ (b i ∘ ContinuousLinearMap.snd ℝ R3 R3) (O1 ×ˢ O2) :=
      ((hbs i).comp_continuousLinearMap (ContinuousLinearMap.snd ℝ R3 R3)).mono fun x hx => hx.2
    exact hf.mul hg
  obtain ⟨r1, hr1, h1⟩ := Metric.isOpen_iff.mp hO1 z.1 hz.1
  obtain ⟨r2, hr2, h2⟩ := Metric.isOpen_iff.mp hO2 z.2 hz.2
  have hK : closedBall z.1 (r1 / 2) ⊆ O1 := (closedBall_subset_ball (half_lt_self hr1)).trans h1
  have hJ : closedBall z.2 (r2 / 2) ⊆ O2 := (closedBall_subset_ball (half_lt_self hr2)).trans h2
  have hU : IsOpen (ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2)) := isOpen_ball.prod isOpen_ball
  have hUKJ : ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2) ⊆
      closedBall z.1 (r1 / 2) ×ˢ closedBall z.2 (r2 / 2) :=
    prod_mono ball_subset_closedBall ball_subset_closedBall
  have hUO : ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2) ⊆ O1 ×ˢ O2 := hUKJ.trans (prod_mono hK hJ)
  have hHs : ∀ k, ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2)
      (ball z.1 (r1 / 2) ×ˢ ball z.2 (r2 / 2)) := fun k =>
    (ContDiffOn.sum fun i _ => hterm i).mono hUO
  obtain ⟨-, hG⟩ := contDiffOn_of_jet_tendstoUniformlyOn _ hU
    (fun k z => ∑ i ∈ t k, W i z.1 * b i z.2) hHs
    (fun m z => ∑' i, iteratedFDeriv ℝ m (fun z : R3 × R3 => W i z.1 * b i z.2) z)
    (fun m => (hjets _ _ (isCompact_closedBall _ _) (isCompact_closedBall _ _) hK hJ m).mono hUKJ)
  have hz' := hG m z ⟨mem_ball_self (half_pos hr1), mem_ball_self (half_pos hr2)⟩
  rw [hH] at hz'
  exact hz'.symm

open MeasureTheory in
/-- SL-8f: the ACTUAL limit `z ↦ ∑' Wᵢ(z.1) bᵢ(z.2)` (actual `Wᵢ`, unnormalized `bᵢ`) of the SAME
partial sums along ANY cofinal `t` is C^∞ on `O1 ×ˢ O2` with jets equal to the `tsum` of term jets. -/
theorem actualSeries_limit_contDiffOn_and_jets (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ)
    (t : ℕ → Finset ι) (ht : Tendsto t atTop atTop) :
    ContDiffOn ℝ ∞ (fun z : R3 × R3 => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) (O1 ×ˢ O2) ∧
      ∀ m : ℕ, ∀ z ∈ O1 ×ˢ O2,
        iteratedFDeriv ℝ m (fun z : R3 × R3 => ∑' i,
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z =
        ∑' i, iteratedFDeriv ℝ m (fun z : R3 × R3 =>
          restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn
            (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
          actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2) z := by
  have hb : ∀ i, ContDiffOn ℝ ∞ (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) D2 := by
    obtain ⟨-, -, -, M, -, harms, -⟩ := h
    exact fun i => (harms i).1
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  exact series_limit_contDiffOn_and_jets O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)
    (fun i => (H1.1 (w i)).1) (fun i => (hb i).mono hO2D2) t
    (fun K J hK hJ hKO1 hJO2 n => actualSeries_jet_tendstoUniformlyOn S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 t ht n)

open MeasureTheory in
/-- SL-9a: a.e. identification of the ONE pointwise limit with a GIVEN `L²(ν)` limit `F` of
classes `v k` a.e. equal to the SAME partial sums (pinned FiniteHarmonicProductL2Limit:561–573). -/
theorem series_limit_ae_eq_of_Lp_tendsto (O1 O2 : Set R3) (hO1 : IsOpen O1) (hO2 : IsOpen O2)
    {ι : Type*} (W b : ι → R3 → ℝ) (t : ℕ → Finset ι)
    (hjets : ∀ K J : Set R3, IsCompact K → IsCompact J → K ⊆ O1 → J ⊆ O2 → ∀ n : ℕ,
      TendstoUniformlyOn
        (fun k z => iteratedFDeriv ℝ n (fun z : R3 × R3 => ∑ i ∈ t k, W i z.1 * b i z.2) z)
        (fun z => ∑' i, iteratedFDeriv ℝ n (fun z : R3 × R3 => W i z.1 * b i z.2) z)
        atTop (K ×ˢ J))
    (v : ℕ → Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)))
    (F : Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)))
    (hlim : Tendsto v atTop (𝓝 F))
    (hv : ∀ k, (v k : R3 × R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
      fun z => ∑ i ∈ t k, W i z.1 * b i z.2) :
    (fun z : R3 × R3 => ∑' i, W i z.1 * b i z.2)
      =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
      (F : R3 × R3 → ℝ) := by
  have hPoint : ∀ z ∈ O1 ×ˢ O2, Tendsto (fun k => ∑ i ∈ t k, W i z.1 * b i z.2) atTop
      (𝓝 (∑' i, W i z.1 * b i z.2)) := by
    intro z hz
    have hu := (hjets {z.1} {z.2} isCompact_singleton isCompact_singleton
      (singleton_subset_iff.2 hz.1) (singleton_subset_iff.2 hz.2) 0).tendsto_at
      (show z ∈ ({z.1} : Set R3) ×ˢ ({z.2} : Set R3) from ⟨rfl, rfl⟩)
    have ht := ((continuousMultilinearCurryFin0 ℝ (R3 × R3) ℝ).continuous.tendsto _).comp hu
    have hc : (continuousMultilinearCurryFin0 ℝ (R3 × R3) ℝ)
        (∑' i, iteratedFDeriv ℝ 0 (fun z : R3 × R3 => W i z.1 * b i z.2) z) =
        ∑' i, W i z.1 * b i z.2 :=
      curry0_tsum_iteratedFDeriv_zero (fun i (z : R3 × R3) => W i z.1 * b i z.2) z
    rw [← hc]
    exact ht.congr (fun k => by simp [Function.comp])
  have hmem : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      z ∈ O1 ×ˢ O2 := by
    have h1 : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod
        ((volume : Measure R3).restrict O2)), z.1 ∈ O1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hO1.measurableSet)
    have h2 : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod
        ((volume : Measure R3).restrict O2)), z.2 ∈ O2 :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hO2.measurableSet)
    filter_upwards [h1, h2] with z hz1 hz2 using ⟨hz1, hz2⟩
  obtain ⟨ns, hns, hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      ∀ k, (v k : R3 × R3 → ℝ) z = ∑ i ∈ t k, W i z.1 * b i z.2 := ae_all_iff.mpr hv
  filter_upwards [hall, hnsAE, hmem] with z hz hnsz hzO
  have hHlim := (hPoint z hzO).comp hns.tendsto_atTop
  have hFlim : Tendsto (fun k => ∑ i ∈ t (ns k), W i z.1 * b i z.2) atTop
      (𝓝 ((F : R3 × R3 → ℝ) z)) := hnsz.congr (fun k => hz (ns k))
  exact tendsto_nhds_unique hHlim hFlim

open MeasureTheory in
/-- SL-9b: the ACTUAL smooth limit of the SAME partial sums along the SAME `s` of
`crossSeries_actual_limit` is a.e. (for `ν = vol|O1 ⊗ vol|O2`) the SAME tensor `L²` limit
`∑' tensorLp (R_{O1} wᵢ) gᵢ`, `gᵢ = [bᵢ]_{O2}`. -/
theorem actualSeries_limit_ae_eq_tensor_limit (S : KnownSideSourceData) (L lam : ℝ)
    (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1 : IsOpen O1) (hO1D1 : O1 ⊆ D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (hO2 : IsOpen O2) (hO2D2 : O2 ⊆ D2)
    {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ) :
    ∃ (g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2)) (s : ℕ → Finset ι),
      (∀ i, actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      Tendsto s atTop atTop ∧
      Tendsto (fun k => ∑ i ∈ s k,
          tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) atTop
        (𝓝 (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))) ∧
      (fun z : R3 × R3 => ∑' i,
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 *
        actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2)
      =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
      ((∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i) :
          Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2))) :
        R3 × R3 → ℝ) := by
  obtain ⟨M, g, s, -, hgae, -, -, hcof, -, hT, hae⟩ :=
    crossSeries_actual_limit S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 w μ h
  have H1 := restrictRep_spec_and_jet_bound D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1
  refine ⟨g, s, hgae, hcof, hT, ?_⟩
  refine series_limit_ae_eq_of_Lp_tendsto O1 O2 hO1 hO2
    (fun i => restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i))
    (fun i => actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) s
    (fun K J hK hJ hKO1 hJO2 n => actualSeries_jet_tendstoUniformlyOn S L lam D1 hD1 O1 hO1
      hO1D1 T hTD1 D2 O2 S2 hO2 hO2D2 w μ h K J hK hJ hKO1 hJO2 s hcof n)
    _ _ hT (fun k => ?_)
  have hW : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      ∀ i ∈ s k, (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i : R3 → ℝ) z.1 =
        restrictRep D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn
          (fun x _ => dilatedFirstPrincipal_posDef S lam x) O1 hO1 hO1D1 (w i) z.1 :=
    (eventually_all_finset (s k)).2 fun i _ =>
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (H1.1 (w i)).2.1.symm
  filter_upwards [hae k, hW] with z hz hzW
  rw [hz]
  exact Finset.sum_congr rfl fun i hi => by rw [hzW i hi]

/-- SL-10a: operator limit (pinned FiniteHarmonicProductL2Limit:600–626 as a standalone lemma):
if `C²` functions `U j` solve `div(A∇·) = 0` at `x` and their first and second derivatives at `x`
converge to those of a `C²` function `U0`, then `U0` solves it at `x`. -/
theorem divCoeffGrad_eq_zero_of_jet_tendsto {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ContDiff ℝ ∞ A) (U : ℕ → R3 → ℝ) (U0 : R3 → ℝ) (x : R3)
    (hU : ∀ j, ContDiffAt ℝ 2 (U j) x) (hU0 : ContDiffAt ℝ 2 U0 x)
    (hP : ∀ j, divCoeffGrad A (U j) x = 0)
    (h1 : ∀ a : R3, Tendsto (fun j => fderiv ℝ (U j) x a) atTop (𝓝 (fderiv ℝ U0 x a)))
    (h2 : ∀ a b : R3, Tendsto (fun j => fderiv ℝ (fderiv ℝ (U j)) x a b) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ U0) x a b))) : divCoeffGrad A U0 x = 0 := by
  have hAt := hA.differentiable (by simp) x
  have ht : Tendsto (fun j => ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun z => A z i k) x (EuclideanSpace.single i 1) *
        fderiv ℝ (U j) x (EuclideanSpace.single k 1) +
      A x i k * fderiv ℝ (fderiv ℝ (U j)) x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)))
      atTop (𝓝 (∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun z => A z i k) x (EuclideanSpace.single i 1) *
        fderiv ℝ U0 x (EuclideanSpace.single k 1) +
      A x i k * fderiv ℝ (fderiv ℝ U0) x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)))) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro k hk
    exact (tendsto_const_nhds.mul (h1 _)).add (tendsto_const_nhds.mul (h2 _ _))
  have ht' : Tendsto (fun j => divCoeffGrad A (U j) x) atTop (𝓝 (divCoeffGrad A U0 x)) := by
    rw [OAI.AnisotropicCalderon.Regularity.Jets.divCoeffGrad_eq_jet hAt hU0]
    exact ht.congr (fun j =>
      (OAI.AnisotropicCalderon.Regularity.Jets.divCoeffGrad_eq_jet hAt (hU j)).symm)
  have he : (fun j => divCoeffGrad A (U j) x) = fun _ : ℕ => (0 : ℝ) := funext hP
  rw [he] at ht'
  exact tendsto_nhds_unique ht' tendsto_const_nhds

end ProductTermJets

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
