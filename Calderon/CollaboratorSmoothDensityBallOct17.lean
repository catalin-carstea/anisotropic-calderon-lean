import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.Wkp.LocalApproximation
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Density of smooth data in `W^{1,2}(B)` on the unit ball (helper for task 11).

The proof dilates `u` to `x ↦ u (c • x)` on the larger ball `ball 0 c⁻¹` (`c < 1`), approximates
the dilation on the compactly contained unit ball by test functions (Tau Ceti's local
approximation theorem), and uses continuity of dilations in `L²` as `c → 1`. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped Distributions ENNReal InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.EnergyBridge
end OAI.AnisotropicCalderon.EnergyBridge

namespace OAI.AnisotropicCalderon.EnergyBridge.SmoothDensityBallAux

/-- Dilate a test function: `y ↦ φ (c⁻¹ • y)`. -/
def dilateTest {Ω V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (Ω : Set R3)) (φ : 𝓓(V, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun y => φ (c⁻¹ • y),
    φ.contDiff.comp (contDiff_const_smul c⁻¹),
    by
      have := φ.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero c⁻¹ (by positivity))
      simpa [Function.comp_def] using this,
    by
      intro y hy
      have hfun : (fun z => φ (c⁻¹ • z)) =
          (φ : R3 → ℝ) ∘ (Homeomorph.smulOfNeZero c⁻¹ (by positivity) : R3 → R3) := by
        funext z; rfl
      have hycomp : y ∈ tsupport
          ((φ : R3 → ℝ) ∘ (Homeomorph.smulOfNeZero c⁻¹ (by positivity) : R3 → R3)) := by
        rw [← hfun]; exact hy
      rw [tsupport_comp_eq_preimage] at hycomp
      have := hVO (φ.tsupport_subset hycomp)
      simpa [smul_smul, hc.ne'] using this⟩

theorem dilateTest_apply {Ω V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (Ω : Set R3)) (φ : 𝓓(V, ℝ)) (y : R3) :
    dilateTest hc hVO φ y = φ (c⁻¹ • y) := rfl

theorem lineDeriv_dilateTest {Ω V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (Ω : Set R3)) (φ : 𝓓(V, ℝ)) (y v : R3) :
    lineDeriv ℝ (dilateTest hc hVO φ : R3 → ℝ) y v =
      c⁻¹ * lineDeriv ℝ (φ : R3 → ℝ) (c⁻¹ • y) v := by
  have hd : Differentiable ℝ (φ : R3 → ℝ) := φ.contDiff.differentiable (by simp)
  have hd' : Differentiable ℝ (dilateTest hc hVO φ : R3 → ℝ) :=
    (dilateTest hc hVO φ).contDiff.differentiable (by simp)
  rw [(hd' y).lineDeriv_eq_fderiv, (hd _).lineDeriv_eq_fderiv]
  have hfun : (dilateTest hc hVO φ : R3 → ℝ) = fun z => φ (c⁻¹ • z) := rfl
  rw [hfun, fderiv_comp_smul (f := (φ : R3 → ℝ)) (x := y) c⁻¹]
  simp


theorem hasWeakLineDerivOn_comp_smul {Ω V : TopologicalSpace.Opens R3} {u u' : R3 → ℝ} {v : R3}
    {c : ℝ} (hc : 0 < c) (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (Ω : Set R3))
    (hu : TauCeti.HasWeakLineDerivOn volume Ω u u' v)
    (hli : LocallyIntegrableOn (fun x => u (c • x)) V volume)
    (hli' : LocallyIntegrableOn (fun x => c • u' (c • x)) V volume) :
    TauCeti.HasWeakLineDerivOn volume V (fun x => u (c • x)) (fun x => c • u' (c • x)) v := by
  rw [TauCeti.hasWeakLineDerivOn_iff hli hli']
  intro φ hφ hφc hφs
  let φt : 𝓓(V, ℝ) := ⟨φ, hφ, hφc, hφs⟩
  let ψ := dilateTest hc hVO φt
  have key := hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  have hA : ∫ x, lineDeriv ℝ φ x v • u (c • x) =
      c * (|(c ^ Module.finrank ℝ R3)⁻¹| * ∫ y, lineDeriv ℝ (ψ : R3 → ℝ) y v • u y) := by
    rw [← smul_eq_mul (a := |(c ^ Module.finrank ℝ R3)⁻¹|),
      ← Measure.integral_comp_smul, ← integral_const_mul]
    congr 1; funext x
    simp only [ψ, lineDeriv_dilateTest, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, smul_eq_mul]
    have : (φt : R3 → ℝ) = φ := rfl
    rw [this]
    field_simp
  have hB : ∫ x, φ x • (c • u' (c • x)) =
      c * (|(c ^ Module.finrank ℝ R3)⁻¹| * ∫ y, (ψ : R3 → ℝ) y • u' y) := by
    rw [← smul_eq_mul (a := |(c ^ Module.finrank ℝ R3)⁻¹|),
      ← Measure.integral_comp_smul, ← integral_const_mul]
    congr 1; funext x
    simp only [ψ, dilateTest_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, smul_eq_mul]
    have : (φt : R3 → ℝ) = φ := rfl
    rw [this]
    ring
  rw [hA, hB, key]
  ring

theorem memLp_comp_smul_restrict {G : Type*} [NormedAddCommGroup G] {f : R3 → G} {p : ℝ≥0∞}
    {Ω V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (Ω : Set R3))
    (hf : MemLp f p ((volume : Measure R3).restrict Ω)) :
    MemLp (fun x => f (c • x)) p ((volume : Measure R3).restrict V) := by
  have h1 : MemLp ((Ω : Set R3).indicator f) p volume :=
    (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2 hf
  have h2 : MemLp ((Ω : Set R3).indicator f ∘ fun x : R3 => c • x) p volume := by
    refine (measurableEmbedding_const_smul₀ hc.ne').memLp_map_measure_iff.1 ?_
    rw [Measure.map_addHaar_smul volume hc.ne']
    exact h1.smul_measure ENNReal.ofReal_ne_top
  refine (h2.restrict (V : Set R3)).ae_eq ?_
  refine ae_restrict_of_forall_mem V.isOpen.measurableSet fun x hx => ?_
  simp only [Function.comp_apply]
  exact indicator_of_mem (hVO hx) f

theorem memLp_dilate_value {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    MemLp (fun x => TauCeti.W1p.value u (c • x)) 2 ((volume : Measure R3).restrict V) :=
  memLp_comp_smul_restrict hc hVO (Lp.memLp _)

theorem memLp_dilate_gradient {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    MemLp (fun x => c • TauCeti.W1p.gradient u (c • x)) 2 ((volume : Measure R3).restrict V) :=
  (memLp_comp_smul_restrict hc hVO (Lp.memLp (TauCeti.W1p.gradient u))).const_smul c

theorem hasWeakFDerivOn_dilate {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    TauCeti.HasWeakFDerivOn volume V ((memLp_dilate_value hc hVO u).toLp _)
      (fun x => innerSL ℝ ((memLp_dilate_gradient hc hVO u).toLp _ x)) := by
  rw [TauCeti.hasWeakFDerivOn_iff]
  intro w
  have hw := (TauCeti.W1p.hasWeakFDerivOn u).hasWeakLineDerivOn w
  have hv := memLp_dilate_value hc hVO u
  have hgi : MemLp (fun x => c • (innerSL ℝ (TauCeti.W1p.gradient u (c • x))) w) 2
      ((volume : Measure R3).restrict V) := by
    have := ((memLp_comp_smul_restrict hc hVO (Lp.memLp (TauCeti.W1p.gradient u))).inner_const (𝕜 := ℝ)
      w).const_smul c
    simpa only [innerSL_apply_apply, Pi.smul_def] using this
  have hli : LocallyIntegrableOn (fun x => TauCeti.W1p.value u (c • x)) V volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hv.locallyIntegrable (by norm_num))
  have hli' : LocallyIntegrableOn
      (fun x => c • (innerSL ℝ (TauCeti.W1p.gradient u (c • x))) w) V volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hgi.locallyIntegrable (by norm_num))
  have h := hasWeakLineDerivOn_comp_smul hc hVO hw hli hli'
  refine (h.congr_ae hv.coeFn_toLp.symm).congr_ae_deriv ?_
  filter_upwards [(memLp_dilate_gradient hc hVO u).coeFn_toLp] with x hx
  rw [hx]
  simp [innerSL_apply_apply]

/-- The dilation `x ↦ u (c • x)` of a Sobolev function on the unit ball. -/
def dilateW1p {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    TauCeti.W1p volume V 2 :=
  TauCeti.W1p.mk _ _ (hasWeakFDerivOn_dilate hc hVO u)

theorem value_dilateW1p_ae {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    TauCeti.W1p.value (dilateW1p hc hVO u) =ᵐ[(volume : Measure R3).restrict V]
      fun x => TauCeti.W1p.value u (c • x) := by
  rw [dilateW1p, TauCeti.W1p.value_mk]
  exact MemLp.coeFn_toLp _

theorem gradient_dilateW1p_ae {V : TopologicalSpace.Opens R3} {c : ℝ} (hc : 0 < c)
    (hVO : MapsTo (fun x : R3 => c • x) (V : Set R3) (ballOpens : Set R3)) (u : BallH1) :
    TauCeti.W1p.gradient (dilateW1p hc hVO u) =ᵐ[(volume : Measure R3).restrict V]
      fun x => c • TauCeti.W1p.gradient u (c • x) := by
  rw [dilateW1p, TauCeti.W1p.gradient_mk]
  exact MemLp.coeFn_toLp _

theorem tendsto_eLpNorm_comp_smul_sub_of_continuous {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : R3 → G} (hg : Continuous g) (hgc : HasCompactSupport g)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {c : ι → ℝ} (hc : Tendsto c l (𝓝 1)) :
    Tendsto (fun i => eLpNorm (fun x => g (c i • x) - g x) p volume) l (𝓝 0) := by
  obtain ⟨R0, hR0⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : R3)
  set R := max R0 0 with hRdef
  have hR : tsupport g ⊆ Metric.closedBall 0 R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR_nonneg : 0 ≤ R := le_max_right _ _
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hb : MemLp ((Metric.closedBall (0 : R3) (2 * R)).indicator fun _ => (1 : ℝ)) p volume :=
    memLp_indicator_const p
      (Metric.isClosed_closedBall (x := (0 : R3)) (ε := 2 * R)).measurableSet.nullMeasurableSet (1 : ℝ)
      (Or.inr (measure_closedBall_lt_top (μ := volume)).ne)
  have hev : ∀ᶠ i in l, c i ∈ Ioo (1 / 2 : ℝ) 2 := hc (Ioo_mem_nhds (by norm_num) (by norm_num))
  have key := TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto hp0 hp
    (f := fun i x => g (c i • x)) (g := g)
    (Eventually.of_forall fun i => (hg.comp (continuous_const_smul _)).aestronglyMeasurable)
    hg.aestronglyMeasurable hb (C := Real.toNNReal (2 * M))
    (hev.mono fun i hi => Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.closedBall (0 : R3) (2 * R)
      · rw [indicator_of_mem hx, enorm_one, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith [hM (c i • x), hM x]))
      · have hx' : R < ‖x‖ := by
          simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx; linarith
        have h1 : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => by
          have := hR h; simp only [Metric.mem_closedBall, dist_zero_right] at this; linarith
        have h2 : g (c i • x) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
          have := hR h
          simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (show (0 : ℝ) < c i by linarith [hi.1])] at this
          simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
          nlinarith [hi.1]
        simp [h1, h2])
    (Eventually.of_forall fun x => by
      have := (hg.tendsto _).comp (hc.smul_const x)
      simpa [Function.comp_def] using this)
  exact key

theorem eLpNorm_comp_smul_le {G : Type*} [NormedAddCommGroup G] (h : R3 → G) {p : ℝ≥0∞}
    {c : ℝ} (hc : 1 / 2 < c) :
    eLpNorm (fun x => h (c • x)) p volume ≤
      ENNReal.ofReal 8 ^ (1 / p).toReal * eLpNorm h p volume := by
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hc; norm_num at hc
  rw [show (fun x => h (c • x)) = h ∘ (fun x : R3 => c • x) from rfl,
    ← (measurableEmbedding_const_smul₀ hc0).eLpNorm_map_measure,
    Measure.map_addHaar_smul volume hc0]
  by_cases h0 : ENNReal.ofReal |(c ^ Module.finrank ℝ R3)⁻¹| = 0
  · rw [h0, zero_smul, eLpNorm_measure_zero]; exact bot_le
  rw [eLpNorm_smul_measure_of_ne_zero h0, smul_eq_mul]
  gcongr
  rw [finrank_euclideanSpace_fin]
  have hcpos : 0 < c := by linarith
  rw [abs_of_pos (by positivity)]
  have : (1 / 8 : ℝ) < c ^ 3 := by
    have := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this ⊢; linarith
  have h8 : (c ^ 3)⁻¹ ≤ 8 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  exact h8

theorem tendsto_eLpNorm_comp_smul_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : R3 → G} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hF : MemLp F p volume)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {c : ι → ℝ} (hc : Tendsto c l (𝓝 1)) :
    Tendsto (fun i => eLpNorm (fun x => F (c i • x) - F x) p volume) l (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  set K : ℝ≥0∞ := ENNReal.ofReal 8 ^ (1 / p).toReal with hKdef
  have hKtop : K ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hK2 : K + 2 ≠ ⊤ := by finiteness
  have hK0 : K + 2 ≠ 0 := by positivity
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set δ := ε / (K + 2) with hδdef
  have hδ : 0 < δ := ENNReal.div_pos hε.ne' hK2
  obtain ⟨g, hgc, hFg, hgcont, hgmem⟩ :=
    MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le hp hF hδ.ne'
  have hconv := tendsto_eLpNorm_comp_smul_sub_of_continuous hgcont hgc hp0 hp hc
  have hev : ∀ᶠ i in l, c i ∈ Ioo (1 / 2 : ℝ) 2 := hc (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hev, (ENNReal.tendsto_nhds_zero.1 hconv) δ hδ] with i hi hgi
  have hsplit : (fun x => F (c i • x) - F x) =
      (fun x => (F - g) (c i • x)) + (fun x => g (c i • x) - g x) + (g - F) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; abel
  calc eLpNorm (fun x => F (c i • x) - F x) p volume
      ≤ eLpNorm (fun x => (F - g) (c i • x)) p volume +
          eLpNorm (fun x => g (c i • x) - g x) p volume + eLpNorm (g - F) p volume := by
        rw [hsplit]
        refine (eLpNorm_add_le hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hp1
    _ ≤ K * δ + δ + δ := by
        gcongr
        · exact (eLpNorm_comp_smul_le _ hi.1).trans (by gcongr)
        · rw [eLpNorm_sub_comm]; exact hFg
    _ = (K + 2) * δ := by ring
    _ = ε := ENNReal.mul_div_cancel hK0 hK2

theorem tendsto_restrict_dilate (u : BallH1) {c : ℕ → ℝ} (hc0 : ∀ k, 0 < c k)
    (hc1 : ∀ k, c k ≤ 1) (hc : Tendsto c atTop (𝓝 1)) {V : ℕ → TopologicalSpace.Opens R3}
    (hVO : ∀ k, MapsTo (fun x : R3 => c k • x) (V k : Set R3) (ballOpens : Set R3))
    (hBV : ∀ k, ballOpens ≤ V k) :
    Tendsto (fun k => TauCeti.W1p.restrictL (hBV k) (dilateW1p (hc0 k) (hVO k) u)) atTop
      (𝓝 u) := by
  have hBmeas : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  have hBB : ∀ k, ∀ x ∈ (ballOpens : Set R3), c k • x ∈ (ballOpens : Set R3) :=
    fun k x hx => hVO k (hBV k hx)
  have hsub : ∀ k, (ballOpens : Set R3) ⊆ (V k : Set R3) := fun k => hBV k
  rw [TauCeti.W1p.tendsto_iff_value_gradient]
  constructor
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    set v : R3 → ℝ := ⇑(TauCeti.W1p.value u)
    set vt : R3 → ℝ := (ballOpens : Set R3).indicator v
    have hvt : MemLp vt 2 volume :=
      (memLp_indicator_iff_restrict hBmeas.nullMeasurableSet).2 (Lp.memLp _)
    have hlim := tendsto_eLpNorm_comp_smul_sub (by norm_num) hvt hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun k => ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (eLpNorm_mono_measure _ Measure.restrict_le_self)
    have h1 := TauCeti.W1p.value_restrictL_ae (hBV k) (dilateW1p (hc0 k) (hVO k) u)
    have h2 := ae_restrict_of_ae_restrict_of_subset (hsub k) (value_dilateW1p_ae (hc0 k) (hVO k) u)
    filter_upwards [h1, h2, ae_restrict_mem hBmeas] with x hx1 hx2 hxB
    simp only [Pi.sub_apply]
    rw [hx1, hx2]
    simp only [vt, indicator_of_mem hxB, indicator_of_mem (hBB k x hxB), v]
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    set G : R3 → R3 := ⇑(TauCeti.W1p.gradient u)
    set Gt : R3 → R3 := (ballOpens : Set R3).indicator G
    have hGt : MemLp Gt 2 volume :=
      (memLp_indicator_iff_restrict hBmeas.nullMeasurableSet).2 (Lp.memLp _)
    have hlim := tendsto_eLpNorm_comp_smul_sub (by norm_num) hGt hc
    have hc' : Tendsto (fun k => ‖c k - 1‖ₑ) atTop (𝓝 0) := by
      have h1 := hc.sub_const 1
      rw [sub_self] at h1
      have := (continuous_enorm.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def] using this
    have hlim2 := ENNReal.Tendsto.mul_const hc' (Or.inr hGt.eLpNorm_ne_top)
    rw [zero_mul] at hlim2
    have hsum := hlim.add hlim2
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le) (fun k => ?_)
    have heq : (⇑(TauCeti.W1p.gradient (TauCeti.W1p.restrictL (hBV k)
        (dilateW1p (hc0 k) (hVO k) u))) - ⇑(TauCeti.W1p.gradient u))
        =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x => c k • (Gt (c k • x) - Gt x)) + (fun x => (c k - 1) • Gt x) := by
      have h1 := TauCeti.W1p.gradient_restrictL_ae (hBV k) (dilateW1p (hc0 k) (hVO k) u)
      have h2 := ae_restrict_of_ae_restrict_of_subset (hsub k)
        (gradient_dilateW1p_ae (hc0 k) (hVO k) u)
      filter_upwards [h1, h2, ae_restrict_mem hBmeas] with x hx1 hx2 hxB
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hx1, hx2]
      simp only [Gt, indicator_of_mem hxB, indicator_of_mem (hBB k x hxB), G]
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [eLpNorm_congr_ae heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    gcongr
    · refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [show (fun x => c k • (Gt (c k • x) - Gt x)) = c k • (fun x => Gt (c k • x) - Gt x)
        from rfl, eLpNorm_const_smul]
      calc ‖c k‖ₑ * eLpNorm (fun x => Gt (c k • x) - Gt x) 2 volume
          ≤ 1 * eLpNorm (fun x => Gt (c k • x) - Gt x) 2 volume := by
            gcongr
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (hc0 k)]
            exact ENNReal.ofReal_le_one.2 (hc1 k)
        _ = _ := one_mul _
    · refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [show (fun x => (c k - 1) • Gt x) = (c k - 1) • Gt from rfl, eLpNorm_const_smul]

theorem restrictL_ofTestFunction_eq {Ω : TopologicalSpace.Opens R3} (h : ballOpens ≤ Ω)
    (φ : 𝓓(Ω, ℝ)) :
    TauCeti.W1p.restrictL h (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ) =
      smoothSobolev ⟨φ, φ.contDiff⟩ := by
  have hsub : (ballOpens : Set R3) ⊆ (Ω : Set R3) := h
  apply TauCeti.W1p.ext
  · apply Lp.ext
    have h1 := TauCeti.W1p.value_restrictL_ae h (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ)
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub
      (TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ)
    have h3 := value_smoothSobolev_ae ⟨φ, φ.contDiff⟩
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1, hx3, TauCeti.W1p.value_ofTestFunctionₗ, hx2]
  · apply Lp.ext
    have h1 := TauCeti.W1p.gradient_restrictL_ae h (TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ)
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub
      (TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ)
    have h3 := gradient_smoothSobolev_ae ⟨φ, φ.contDiff⟩
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx1, hx3, TauCeti.W1p.gradient_ofTestFunctionₗ, hx2]

end OAI.AnisotropicCalderon.EnergyBridge.SmoothDensityBallAux

namespace OAI.AnisotropicCalderon.EnergyBridge

open SmoothDensityBallAux in
/-- Every element of `BallH1` is a limit of jets of globally smooth functions. -/
theorem exists_smoothSobolev_tendsto (u : BallH1) :
    ∃ f : ℕ → SmoothData, Tendsto (fun n => smoothSobolev (f n)) atTop (𝓝 u) := by
  set c : ℕ → ℝ := fun k => 1 - 1 / (2 * ((k : ℝ) + 1)) with hcdef
  have hpos : ∀ k : ℕ, 0 < 2 * ((k : ℝ) + 1) := fun k => by positivity
  have hc0 : ∀ k, 0 < c k := fun k => by
    have : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    simp only [hcdef]; linarith
  have hc1 : ∀ k, c k < 1 := fun k => by
    have := one_div_pos.2 (hpos k)
    simp only [hcdef]; linarith
  have hc : Tendsto c atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    have h' := h.const_sub (1 : ℝ)
    simp only [mul_zero, sub_zero] at h'
    refine h'.congr fun k => ?_
    simp only [hcdef]
    field_simp
  let V : ℕ → TopologicalSpace.Opens R3 := fun k => ⟨Metric.ball 0 (c k)⁻¹, Metric.isOpen_ball⟩
  have hVcoe : ∀ k, (V k : Set R3) = Metric.ball 0 (c k)⁻¹ := fun k => rfl
  have hone : ∀ k, 1 < (c k)⁻¹ := fun k => (one_lt_inv₀ (hc0 k)).2 (hc1 k)
  have hVO : ∀ k, MapsTo (fun x : R3 => c k • x) (V k : Set R3) (ballOpens : Set R3) := by
    intro k x hx
    rw [hVcoe, Metric.mem_ball, dist_zero_right] at hx
    simp only [coe_ballOpens, B, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hc0 k)]
    calc c k * ‖x‖ < c k * (c k)⁻¹ := mul_lt_mul_of_pos_left hx (hc0 k)
      _ = 1 := mul_inv_cancel₀ (hc0 k).ne'
  have hclosure : ∀ k, closure (ballOpens : Set R3) ⊆ (V k : Set R3) := by
    intro k
    rw [coe_ballOpens, B, closure_ball (0 : R3) one_ne_zero, hVcoe]
    exact Metric.closedBall_subset_ball (hone k)
  have hcompact : IsCompact (closure (ballOpens : Set R3)) := by
    rw [coe_ballOpens, B, closure_ball (0 : R3) one_ne_zero]
    exact isCompact_closedBall 0 1
  have hBV : ∀ k, ballOpens ≤ V k := fun k =>
    SetLike.coe_subset_coe.mp (subset_closure.trans (hclosure k))
  have hw := tendsto_restrict_dilate u hc0 (fun k => (hc1 k).le) hc hVO hBV
  have hmem : ∀ k, TauCeti.W1p.restrictL (hBV k) (dilateW1p (hc0 k) (hVO k) u) ∈
      closure (Set.range (fun ψ : 𝓓(V k, ℝ) =>
        TauCeti.W1p.restrictL (hBV k) (TauCeti.W1p.ofTestFunctionₗ volume (V k) 2 ψ))) :=
    fun k => TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ (mu := volume) (p := 2)
      (by norm_num) hcompact (hclosure k) (dilateW1p (hc0 k) (hVO k) u)
  have hex : ∀ k, ∃ ψ : 𝓓(V k, ℝ),
      dist (TauCeti.W1p.restrictL (hBV k) (dilateW1p (hc0 k) (hVO k) u))
        (TauCeti.W1p.restrictL (hBV k) (TauCeti.W1p.ofTestFunctionₗ volume (V k) 2 ψ)) <
        1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨b, ⟨ψ, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 (hmem k) (1 / ((k : ℝ) + 1))
      (by positivity)
    exact ⟨ψ, hb⟩
  choose ψ hψ using hex
  refine ⟨fun k => ⟨ψ k, (ψ k).contDiff⟩, ?_⟩
  refine hw.congr_dist ?_
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hlim
  rw [← restrictL_ofTestFunction_eq (hBV k) (ψ k)]
  exact (hψ k).le

end OAI.AnisotropicCalderon.EnergyBridge
