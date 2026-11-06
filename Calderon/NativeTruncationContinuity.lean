import Calderon.NativeTruncationJetContinuity
import Mathlib.MeasureTheory.Function.UnifTight

/-! EXPANSION.json precedes this transparent exact pinned-proof partition. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E]
variable [MeasurableSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Truncation above a nonnegative level is continuous in the Sobolev norm for finite
exponents. -/
lemma continuous_nativePosPartAbove (hp : p ≠ ∞) {k : ℝ} (hk : 0 ≤ k) :
    Continuous (W1p.posPartAbove (mu := mu) (Omega := Omega) hp hk) := by
  rw [continuous_iff_seqContinuous]
  intro a u ha
  apply tendsto_subtype_rng.mpr
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hsrc : Tendsto (fun n ↦ (a (ns n) : Sobolev1JetLp mu Omega p)) atTop
      (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    (tendsto_subtype_rng.mp ha).comp hns
  -- An almost-everywhere convergent subsequence identifies the truncated limit.
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hsrc).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  let f : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ a (ns (ms n))
  let g : ℕ → Sobolev1JetLp mu Omega p := fun n ↦ W1p.posPartAbove hp hk (a (ns (ms n)))
  have hf : Tendsto f atTop (𝓝 (u : Sobolev1JetLp mu Omega p)) :=
    hsrc.comp hms.tendsto_atTop
  have hvitali := (tendstoInMeasure_iff_tendsto_Lp (Fact.out : 1 ≤ p) hp
    (fun n ↦ Lp.memLp (f n)) (Lp.memLp (u : Sobolev1JetLp mu Omega p))).mpr
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hf)
  have hnorm (n : ℕ) : ∀ᵐ x ∂mu.restrict Omega, ‖g n x‖ ≤ ‖f n x‖ := by
    filter_upwards [posPartAbove_coe_ae hp hk (a (ns (ms n)))] with x hx
    dsimp only [g, f]
    rw [hx]
    exact norm_posPartAboveJet_le hk _
  have hui : UnifIntegrable (fun n x ↦ g n x) p (mu.restrict Omega) :=
    hvitali.2.1.ae_mono (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable) fun n ↦
      (hnorm n).mono fun x hx ↦ by
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hx
  have hut : UnifTight (fun n x ↦ g n x) p (mu.restrict Omega) := by
    intro ε hε
    obtain ⟨s, hs, hfinite, hbound⟩ := hvitali.2.2.exists_measurableSet_indicator hε.ne'
    refine ⟨s, hfinite.ne, fun n ↦ (eLpNorm_mono_ae
      ((Lp.memLp (g n)).aestronglyMeasurable.indicator hs.compl) ?_).trans (hbound n)⟩
    filter_upwards [hnorm n] with x hx
    by_cases hxs : x ∈ sᶜ
    · simpa only [Set.indicator_of_mem hxs] using hx
    · simp only [Set.indicator_of_notMem hxs, norm_zero, le_refl]
  -- The only discontinuity of the jet truncation disappears on Sobolev level sets.
  have hzero : ∀ᵐ x ∂mu.restrict Omega,
      ((u : Sobolev1JetLp mu Omega p) x).fst = k →
        ((u : Sobolev1JetLp mu Omega p) x).snd = 0 := by
    filter_upwards [W1p.value_apply_ae u, W1p.gradient_apply_ae u,
      W1p.gradient_ae_eq_zero_on_level_set hp u k] with x hv hg hz
    intro hx
    rw [← hg]
    exact hz (hv.trans hx)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  apply tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ p) hp
    (fun n ↦ (Lp.memLp (g n)).aestronglyMeasurable)
    (Lp.memLp (W1p.posPartAbove hp hk u : Sobolev1JetLp mu Omega p)) hui hut
  filter_upwards [hae, hzero,
    ae_all_iff.mpr (fun n ↦ posPartAbove_coe_ae hp hk (a (ns (ms n)))),
    posPartAbove_coe_ae hp hk u] with x hx hz hg hu
  rw [hu]
  exact ((continuousAt_posPartAboveJet k hz).tendsto.comp hx).congr'
    (Eventually.of_forall fun n ↦ (hg n).symm)

/-- Taking the positive part is continuous in the Sobolev norm for finite exponents. -/
lemma continuous_nativePosPart (hp : p ≠ ∞) :
    Continuous (W1p.posPart (mu := mu) (Omega := Omega) hp) := by
  exact (continuous_nativePosPartAbove (mu := mu) (Omega := Omega) hp (le_refl 0)).congr
    (W1p.posPartAbove_zero hp)

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuous_nativePosPartAbove
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.continuous_nativePosPart
